/**
 * Minimal JS implementation of sr25519 cryptography for Polkadot.
 *
 * Uses [Merlin](https://merlin.cool/index.html),
 * a transcript construction, built on [Strobe](https://strobe.sourceforge.io).
 * Merlin ensures two parties agree on the same state when communicating.
 *
 * More: https://wiki.polkadot.network/docs/learn-cryptography.
 */
import { mod } from '@noble/curves/abstract/modular.js';
import { ed25519, ristretto255, ristretto255_hasher } from '@noble/curves/ed25519.js';
import {
  aInRange,
  bitMask,
  bytesToNumberLE,
  equalBytes,
  isBytes,
  numberToBytesLE,
} from '@noble/curves/utils.js';
import { sha512 } from '@noble/hashes/sha2.js';
import { keccakP } from '@noble/hashes/sha3.js';
import {
  concatBytes,
  randomBytes,
  u32,
  utf8ToBytes,
  type TArg,
  type TRet,
} from '@noble/hashes/utils.js';

// prettier-ignore
const _0n = /* @__PURE__ */ BigInt(0), _3n = /* @__PURE__ */ BigInt(3);
const RistrettoPoint = /* @__PURE__ */ (() => ristretto255.Point)();
type Point = typeof ristretto255.Point.BASE;
type Data = string | Uint8Array;

function toData(d: TArg<Data>): TRet<Uint8Array> {
  // Merlin/STROBE operate on byte strings.
  // JS strings are accepted here only as a UTF-8 convenience wrapper.
  if (typeof d === 'string') return utf8ToBytes(d) as TRet<Uint8Array>;
  if (isBytes(d)) return d as TRet<Uint8Array>;
  throw new TypeError('Wrong data');
}
// Could've used bytes from hashes/assert, but we add extra arg
function abytes(title: string, b: TArg<Uint8Array>, ...lengths: number[]) {
  // Fixed-width wire formats pass explicit lengths.
  // Raw transcript/message inputs only need the byte-string check.
  if (!isBytes(b)) throw new TypeError(`${title}: Uint8Array expected`);
  if (lengths.length && !lengths.includes(b.length))
    throw new RangeError(
      `${title}: Uint8Array expected of length ${lengths}, not of length=${b.length}`
    );
}

function checkU32(title: string, n: number) {
  // Merlin frames message, challenge, and witness lengths with LE32,
  // so these counts must stay within unsigned 32-bit range.
  if (typeof n !== 'number') throw new TypeError(`${title}: wrong u32 integer: ${n}`);
  if (!Number.isSafeInteger(n) || n < 0 || n > 0xff_ff_ff_ff)
    throw new RangeError(`${title}: wrong u32 integer: ${n}`);
  return n;
}

function cleanBytes(...list: TArg<Uint8Array[]>): void {
  // Wipe temporary secret buffers in place once the caller no longer needs them.
  for (const t of list) t.fill(0);
}

// Shared empty byte string for transcript steps and default ctx/extra values that
// intentionally commit no payload.
const EMPTY = /* @__PURE__ */ Uint8Array.of();
// RFC 9496 §4.4: ristretto255 scalars live modulo the subgroup order l.
const CURVE_ORDER = /* @__PURE__ */ (() => ed25519.Point.Fn.ORDER)();
function parseScalar(title: string, bytes: TArg<Uint8Array>) {
  // Parse canonical 32-byte little-endian scalars; callers that need reduction use modN instead.
  abytes(title, bytes, 32);
  const n = bytesToNumberLE(bytes);
  aInRange(title, n, _0n, CURVE_ORDER);
  return n;
}
// Reduce wide transcript outputs and scalar expressions modulo the ristretto255 order.
const modN = (n: bigint) => mod(n, CURVE_ORDER);
// STROBE128 (minimal version required for Merlin)
// - https://strobe.sourceforge.io/specs/
// We can implement full version, but seems nobody uses this much.
// Strobe-128 over Keccak-f/1600 uses r/8 = 168 bytes and reserves 2 framing bytes,
// leaving 166 user-data bytes.
const STROBE_R: number = 166;
// STROBE beginOp uses the flag order (I, A, C, T, M, K), with M transcript-only and
// K as the key-tree extension bit.
const Flags = /* @__PURE__ */ (() =>
  ({
    I: 1,
    A: 1 << 1,
    C: 1 << 2,
    T: 1 << 3,
    M: 1 << 4,
    K: 1 << 5,
  }) as const)();

// Differences: suffix, additional methods/flags
// Minimal STROBE-128 subset for Merlin: metadata / AD / PRF / KEY only,
// with transport operations intentionally unsupported.
class Strobe128 {
  state: Uint8Array = new Uint8Array(200);
  state32: Uint32Array;
  pos: number = 0;
  posBegin: number = 0;
  curFlags: number = 0;
  constructor(protocolLabel: Data) {
    this.state.set([1, STROBE_R + 2, 1, 0, 1, 96], 0);
    this.state.set(utf8ToBytes('STROBEv1.0.2'), 6);
    this.state32 = u32(this.state);
    this.keccakF1600();
    this.metaAD(protocolLabel, false);
  }
  private keccakF1600(): void {
    keccakP(this.state32);
  }
  private runF(): void {
    // STROBE A.2: finalize the current block with p_begin, DDATA, and DRATE before applying F.
    this.state[this.pos] ^= this.posBegin;
    this.state[this.pos + 1] ^= 0x04;
    this.state[STROBE_R + 1] ^= 0x80;
    this.keccakF1600();
    this.pos = 0;
    this.posBegin = 0;
  }
  // keccak.update()
  private absorb(data: Uint8Array): void {
    for (let i = 0; i < data.length; i++) {
      this.state[this.pos++] ^= data[i];
      if (this.pos === STROBE_R) this.runF();
    }
  }
  // keccak.xof()
  private squeeze(len: number): Uint8Array {
    const data = new Uint8Array(len);
    for (let i = 0; i < data.length; i++) {
      // PRF uses zero input bytes, so duplex emits state[pos] and then overwrites
      // the consumed lane with zero.
      data[i] = this.state[this.pos];
      this.state[this.pos++] = 0;
      if (this.pos === STROBE_R) this.runF();
    }
    return data;
  }
  private overwrite(data: Uint8Array): void {
    for (let i = 0; i < data.length; i++) {
      // KEY uses the C=1,T=0 branch, so duplex overwrites the state lane with the input byte.
      this.state[this.pos++] = data[i];
      if (this.pos === STROBE_R) this.runF();
    }
  }
  private beginOp(flags: number, more: boolean): void {
    if (more) {
      // Streaming continuation: do not re-emit beginOp framing, but require the
      // same logical operation flags.
      if (this.curFlags !== flags) {
        throw new Error(
          `Continued op with changed flags from ${this.curFlags.toString(2)} to ${flags.toString(2)}`
        );
      }
      return;
    }
    if ((flags & Flags.T) !== 0) throw new Error('T flag is not supported');
    const oldBegin = this.posBegin;
    this.posBegin = this.pos + 1;
    this.curFlags = flags;
    this.absorb(new Uint8Array([oldBegin, flags]));
    const forceF = (flags & (Flags.C | Flags.K)) !== 0;
    if (forceF && this.pos !== 0) this.runF();
  }
  // Public API
  metaAD(data: Data, more: boolean): void {
    this.beginOp(Flags.M | Flags.A, more);
    this.absorb(toData(data));
  }
  AD(data: Data, more: boolean): void {
    this.beginOp(Flags.A, more);
    this.absorb(toData(data));
  }
  PRF(len: number, more: boolean): Uint8Array {
    this.beginOp(Flags.I | Flags.A | Flags.C, more);
    return this.squeeze(len);
  }
  KEY(data: Data, more: boolean): void {
    this.beginOp(Flags.A | Flags.C, more);
    this.overwrite(toData(data));
  }
  // Utils
  clone(): Strobe128 {
    // Allocate a fresh state/state32 pair, then overwrite it with this snapshot
    // so the clone shares no backing storage.
    const n = new Strobe128('0'); // tmp
    n.pos = this.pos;
    n.posBegin = this.posBegin;
    n.state.set(this.state);
    n.curFlags = this.curFlags;
    return n;
  }
  clean(): void {
    this.state.fill(0); // also clears state32, because same buffer
    this.pos = 0;
    this.curFlags = 0;
    this.posBegin = 0;
  }
}
// /STROBE128

// Merlin
// https://merlin.cool/index.html
class Merlin {
  strobe: Strobe128;
  constructor(label: Data) {
    this.strobe = new Strobe128('Merlin v1.0');
    this.appendMessage('dom-sep', label);
  }
  appendMessage(label: Data, message: Data): void {
    this.strobe.metaAD(label, false);
    checkU32('Merlin.appendMessage', message.length);
    // Merlin frames label || LE32(len) as one continued meta-AD operation before the AD payload.
    this.strobe.metaAD(numberToBytesLE(message.length, 4), true);
    this.strobe.AD(message, false);
  }
  challengeBytes(label: Data, len: number): Uint8Array {
    this.strobe.metaAD(label, false);
    checkU32('Merlin.challengeBytes', len);
    // Merlin frames label || LE32(len) as one continued meta-AD operation before the PRF output.
    this.strobe.metaAD(numberToBytesLE(len, 4), true);
    return this.strobe.PRF(len, false);
  }
  clean(): void {
    this.strobe.clean();
  }
}
// /Merlin
// Merlin signging context/transcript (sr25519 specific stuff, Merlin and Strobe
// are generic (but minimal))
class SigningContext extends Merlin {
  constructor(name: string) {
    // Seed the transcript name here; the empty-label signing-context payload is
    // appended later via label(...).
    super(name);
  }
  label(label: Data): void {
    this.appendMessage('', label);
  }
  bytes(bytes: Uint8Array): this {
    // Unlike schnorrkel's reusable base-context helper, this minimal port mutates the
    // live transcript and returns it for chaining.
    this.appendMessage('sign-bytes', bytes);
    return this;
  }
  protoName(label: Data): void {
    this.appendMessage('proto-name', label);
  }
  commitPoint(label: Data, point: Point): void {
    this.appendMessage(label, point.toBytes());
  }
  challengeScalar(label: Data): bigint {
    // Schnorrkel challenge scalars use 64 transcript bytes reduced modulo the ristretto255 order.
    return modN(bytesToNumberLE(this.challengeBytes(label, 64)));
  }
  witnessScalar(label: Data, random: Uint8Array, nonceSeeds: Uint8Array[] = []): bigint {
    // Schnorrkel witness scalars use 64 transcript-RNG bytes reduced modulo the
    // ristretto255 order.
    return modN(bytesToNumberLE(this.witnessBytes(label, 64, random, nonceSeeds)));
  }
  witnessBytes(
    label: Data,
    len: number,
    random: Uint8Array,
    nonceSeeds: Uint8Array[] = []
  ): Uint8Array {
    checkU32('SigningContext.witnessBytes', len);
    const strobeRng = this.strobe.clone();
    for (const ns of nonceSeeds) {
      strobeRng.metaAD(label, false);
      checkU32('SigningContext.witnessBytes nonce length', ns.length);
      strobeRng.metaAD(numberToBytesLE(ns.length, 4), true);
      strobeRng.KEY(ns, false);
    }
    abytes('random', random, 32);
    strobeRng.metaAD('rng', false);
    strobeRng.KEY(random, false);
    // TranscriptRng output is unlabeled: commit only LE32(len) before the final PRF extraction.
    strobeRng.metaAD(numberToBytesLE(len, 4), false);
    return strobeRng.PRF(len, false);
  }
}
// /Merlin signing context

const MASK = /* @__PURE__ */ bitMask(256);
// Serialize the internal scalar in the Ed25519-style secret-key form expected by
// polkadot-js / schnorrkel `to_ed25519_bytes()`.
// == (n * CURVE.h) % CURVE_BIT_MASK
// MULTIPLY BY COFACTOR (x<<3n === x*8n)
const encodeScalar = (n: bigint) => numberToBytesLE((n << _3n) & MASK, 32);
// Parse the Ed25519-style secret-key scalar half back into the internal scalar by
// dividing away the cofactor.
// https://github.com/paritytech/schnorrkel/blob/98b9cef8abce87833a53daec6bee9ec6f75c7aff/src/keys.rs#L537-L539
// DIVIDE BY COFACTOR (x>>3n === x/8n)
const decodeScalar = (n: TArg<Uint8Array>) => bytesToNumberLE(n) >> _3n;

// NOTE: secretKey is 64 bytes (key + nonce). This required for HDKD, since key can be
// derived not only from seed, but from other keys.
/**
 * Derives the public key for an sr25519 secret key.
 * @param secretKey - 64-byte secret key returned by `secretFromSeed()`
 * @returns 32-byte sr25519 public key
 * @throws On wrong argument types. {@link TypeError}
 * @throws On wrong argument lengths. {@link RangeError}
 * @example
 * Derive the public key bytes for a freshly expanded sr25519 secret key.
 * ```ts
 * import { getPublicKey, secretFromSeed } from '@scure/sr25519';
 * import { randomBytes } from '@noble/hashes/utils.js';
 * const secretKey = secretFromSeed(randomBytes(32));
 * getPublicKey(secretKey);
 * ```
 */
export function getPublicKey(secretKey: TArg<Uint8Array>): TRet<Uint8Array> {
  abytes('secretKey', secretKey, 64);
  const scalar = decodeScalar(secretKey.subarray(0, 32));
  return RistrettoPoint.BASE.multiply(scalar).toBytes();
}
/**
 * Expands a 32-byte seed into a 64-byte sr25519 secret key.
 * @param seed - 32-byte seed
 * @returns 64-byte secret key
 * @throws On wrong argument types. {@link TypeError}
 * @throws On wrong argument lengths. {@link RangeError}
 * @example
 * Turn seed material into the sr25519 secret-key format used by the rest of the API.
 * ```ts
 * import { secretFromSeed } from '@scure/sr25519';
 * import { randomBytes } from '@noble/hashes/utils.js';
 * secretFromSeed(randomBytes(32));
 * ```
 */
export function secretFromSeed(seed: TArg<Uint8Array>): TRet<Uint8Array> {
  abytes('seed', seed, 32);
  const r = sha512(seed);
  // Match schnorrkel's Ed25519-compatible seed expansion before normalizing into this
  // package's secret-key byte format.
  // NOTE: different from ed25519
  r[0] &= 248;
  r[31] &= 63;
  r[31] |= 64;
  // this will strip upper 3 bits and lower 3 bits
  const key = encodeScalar(decodeScalar(r.subarray(0, 32)));
  const nonce = r.subarray(32, 64);
  const res = concatBytes(key, nonce);
  cleanBytes(key, nonce, r);
  return res;
}
// Seems like ed25519 keypair? Generates keypair from other keypair in ed25519 format
// NOTE: not exported from wasm. Do we need this at all?
/**
 * Converts a schnorrkel-style 96-byte keypair into the sr25519 key format used by this package.
 * @param pair - 96-byte keypair in schnorrkel
 * `to_half_ed25519_bytes()` layout: `secret.to_ed25519_bytes() || public.to_bytes()`
 * @returns 96-byte normalized keypair
 * @throws If the embedded public key does not match the secret key material. {@link Error}
 * @throws On wrong argument types. {@link TypeError}
 * @throws On wrong argument lengths. {@link RangeError}
 * @example
 * Normalize a compatible 96-byte keypair assembled from this package's secret/public key outputs.
 * ```ts
 * import { fromKeypair, getPublicKey, secretFromSeed } from '@scure/sr25519';
 * import { concatBytes, randomBytes } from '@noble/hashes/utils.js';
 * // Build the package's 64-byte secret format: scalar || nonce.
 * const secretKey = secretFromSeed(randomBytes(32));
 * // Assemble the 96-byte pair accepted by fromKeypair(): secret || pub.
 * const pair = concatBytes(secretKey, getPublicKey(secretKey));
 * // Re-encode and validate the pair before passing it to other APIs.
 * const normalized = fromKeypair(pair);
 * // Reuse the normalized 64-byte secret half with package APIs.
 * const publicKey = getPublicKey(normalized.subarray(0, 64));
 * ```
 */
export function fromKeypair(pair: TArg<Uint8Array>): TRet<Uint8Array> {
  abytes('keypair', pair, 96);
  const sk = pair.subarray(0, 32);
  const nonce = pair.subarray(32, 64);
  const pubBytes = pair.subarray(64, 96);
  // Decode first: the half-ed25519 secret half is already cofactor-shifted, so
  // re-encoding raw bytes would multiply by 8 twice.
  const key = encodeScalar(decodeScalar(sk));
  const realPub = getPublicKey(pair.subarray(0, 64));
  if (!equalBytes(pubBytes, realPub)) throw new Error('wrong public key');
  // No need to clean since subarray's
  return concatBytes(key, nonce, realPub);
}

// Basic sign. NOTE: context is currently constant. Please open issue if you need different one.
const SUBSTRATE_CONTEXT = /* @__PURE__ */ utf8ToBytes('substrate');
/**
 * Signs a message with sr25519.
 * @param secretKey - 64-byte secret key returned by `secretFromSeed()`
 * @param message - message bytes to sign
 * @param random - optional 32-byte nonce seed
 * @returns 64-byte signature
 * @throws On malformed sr25519 key or point data during signing. {@link Error}
 * @throws On wrong argument types. {@link TypeError}
 * @throws On wrong argument lengths. {@link RangeError}
 * @example
 * Sign a message with sr25519, using built-in nonce generation.
 * ```ts
 * import { secretFromSeed, sign } from '@scure/sr25519';
 * import { randomBytes } from '@noble/hashes/utils.js';
 * const secretKey = secretFromSeed(randomBytes(32));
 * sign(secretKey, new Uint8Array([1, 2, 3]));
 * ```
 */
export function sign(
  secretKey: TArg<Uint8Array>,
  message: TArg<Uint8Array>,
  random: TArg<Uint8Array> = randomBytes(32)
): TRet<Uint8Array> {
  abytes('message', message);
  abytes('secretKey', secretKey, 64);
  const t = new SigningContext('SigningContext');
  t.label(SUBSTRATE_CONTEXT);
  t.bytes(message);
  const keyScalar = decodeScalar(secretKey.subarray(0, 32));
  const nonce = secretKey.subarray(32, 64);
  const pubPoint = RistrettoPoint.fromBytes(getPublicKey(secretKey));
  // Bind the signer public key before nonce derivation so witness bytes stay tied to
  // the actual signing key.
  t.protoName('Schnorr-sig');
  t.commitPoint('sign:pk', pubPoint);
  const r = t.witnessScalar('signing', random, [nonce]);
  const R = RistrettoPoint.BASE.multiply(r);
  t.commitPoint('sign:R', R);
  const k = t.challengeScalar('sign:c');
  const s = modN(k * keyScalar + r);
  const res = concatBytes(R.toBytes(), numberToBytesLE(s, 32));
  res[63] |= 128; // add Schnorrkel marker
  t.clean();
  return res;
}
/**
 * Verifies an sr25519 signature.
 * @param message - message bytes that were signed
 * @param signature - 64-byte signature returned by `sign()`
 * @param publicKey - 32-byte public key returned by `getPublicKey()`
 * @returns `true` when the signature is valid
 * @throws If the signature marker or decoded sr25519 point data is invalid. {@link Error}
 * @throws On wrong argument types. {@link TypeError}
 * @throws On wrong argument lengths. {@link RangeError}
 * @example
 * Verify the signature against the same message and derived public key.
 * ```ts
 * import { getPublicKey, secretFromSeed, sign, verify } from '@scure/sr25519';
 * import { randomBytes } from '@noble/hashes/utils.js';
 * const secretKey = secretFromSeed(randomBytes(32));
 * const message = new Uint8Array([1, 2, 3]);
 * const signature = sign(secretKey, message);
 * verify(message, signature, getPublicKey(secretKey));
 * ```
 */
export function verify(
  message: TArg<Uint8Array>,
  signature: TArg<Uint8Array>,
  publicKey: TArg<Uint8Array>
): boolean {
  abytes('message', message);
  abytes('signature', signature, 64);
  abytes('publicKey', publicKey, 32);
  if ((signature[63] & 0b1000_0000) === 0) throw new Error('Schnorrkel marker missing');
  const sBytes = Uint8Array.from(signature.subarray(32, 64)); // copy before modification
  sBytes[31] &= 0b0111_1111; // remove Schnorrkel marker
  const R = RistrettoPoint.fromBytes(signature.subarray(0, 32));
  const s = bytesToNumberLE(sBytes);
  aInRange('s', s, _0n, CURVE_ORDER); // Just in case, it will be checked at multiplication later
  const t = new SigningContext('SigningContext');
  t.label(SUBSTRATE_CONTEXT);
  t.bytes(message);
  const pubPoint = RistrettoPoint.fromBytes(publicKey);
  if (pubPoint.equals(RistrettoPoint.ZERO)) return false;
  t.protoName('Schnorr-sig');
  t.commitPoint('sign:pk', pubPoint);
  t.commitPoint('sign:R', R);
  const k = t.challengeScalar('sign:c');
  const sP = RistrettoPoint.BASE.multiply(s);
  const RR = pubPoint.negate().multiply(k).add(sP);
  t.clean();
  cleanBytes(sBytes);
  return RR.equals(R);
}
/**
 * Computes an sr25519 shared secret.
 * @param secretKey - 64-byte secret key returned by `secretFromSeed()`
 * @param publicKey - peer 32-byte public key
 * @returns 32-byte shared secret
 * @throws If the peer public key is invalid or encodes the identity point. {@link Error}
 * @throws On wrong argument types. {@link TypeError}
 * @throws On wrong argument lengths. {@link RangeError}
 * @example
 * Compute the shared secret from one party's secret key and the other party's public key.
 * ```ts
 * import { getPublicKey, getSharedSecret, secretFromSeed } from '@scure/sr25519';
 * import { randomBytes } from '@noble/hashes/utils.js';
 * const alice = secretFromSeed(randomBytes(32));
 * const bob = secretFromSeed(randomBytes(32));
 * getSharedSecret(alice, getPublicKey(bob));
 * ```
 */
export function getSharedSecret(
  secretKey: TArg<Uint8Array>,
  publicKey: TArg<Uint8Array>
): TRet<Uint8Array> {
  abytes('secretKey', secretKey, 64);
  abytes('publicKey', publicKey, 32);
  const keyScalar = decodeScalar(secretKey.subarray(0, 32));
  const pubPoint = RistrettoPoint.fromBytes(publicKey);
  if (pubPoint.equals(RistrettoPoint.ZERO)) throw new Error('wrong public key (infinity)');
  return pubPoint.multiply(keyScalar).toBytes();
}

// Derive
/**
 * Hierarchical deterministic key derivation helpers for sr25519.
 * @example
 * Derive a hardened child secret using a random 32-byte chain code.
 * ```ts
 * import { HDKD, secretFromSeed } from '@scure/sr25519';
 * import { randomBytes } from '@noble/hashes/utils.js';
 * const secretKey = secretFromSeed(randomBytes(32));
 * HDKD.secretHard(secretKey, randomBytes(32));
 * ```
 */
export const HDKD: TRet<{
  secretSoft(secretKey: Uint8Array, chainCode: Uint8Array, random?: Uint8Array): Uint8Array;
  publicSoft(publicKey: Uint8Array, chainCode: Uint8Array): Uint8Array;
  secretHard(secretKey: Uint8Array, chainCode: Uint8Array): Uint8Array;
}> = /* @__PURE__ */ Object.freeze({
  secretSoft(secretKey, chainCode, random = randomBytes(32)) {
    abytes('secretKey', secretKey, 64);
    abytes('chainCode', chainCode, 32);
    const masterScalar = decodeScalar(secretKey.subarray(0, 32));
    const masterNonce = secretKey.subarray(32, 64);
    const pubPoint = RistrettoPoint.fromBytes(getPublicKey(secretKey));
    const t = new SigningContext('SchnorrRistrettoHDKD');
    t.bytes(EMPTY);
    t.appendMessage('chain-code', chainCode);
    t.commitPoint('public-key', pubPoint);
    const scalar = t.challengeScalar('HDKD-scalar');
    const hdkdChainCode = t.challengeBytes('HDKD-chaincode', 32);
    const nonceSeed = concatBytes(numberToBytesLE(masterScalar, 32), masterNonce);
    const nonce = t.witnessBytes('HDKD-nonce', 32, random, [masterNonce, nonceSeed]);
    const key = encodeScalar(modN(masterScalar + scalar));
    const res = concatBytes(key, nonce);
    cleanBytes(key, nonce, nonceSeed, hdkdChainCode);
    t.clean();
    return res;
  },
  publicSoft(publicKey, chainCode) {
    abytes('publicKey', publicKey, 32);
    abytes('chainCode', chainCode, 32);
    const pubPoint = RistrettoPoint.fromBytes(publicKey);
    const t = new SigningContext('SchnorrRistrettoHDKD');
    t.bytes(EMPTY);
    t.appendMessage('chain-code', chainCode);
    t.commitPoint('public-key', pubPoint);
    const scalar = t.challengeScalar('HDKD-scalar');
    // Consume the companion chain code even though this API returns only the child public key,
    // to mirror schnorrkel/polkadot derivation order.
    t.challengeBytes('HDKD-chaincode', 32);
    t.clean();
    return pubPoint.add(RistrettoPoint.BASE.multiply(scalar)).toBytes();
  },
  secretHard(secretKey, chainCode) {
    abytes('secretKey', secretKey, 64);
    abytes('chainCode', chainCode, 32);
    // Hard derivation hashes the canonical internal scalar bytes, not the Ed25519-style
    // serialized secret half.
    const key = numberToBytesLE(decodeScalar(secretKey.subarray(0, 32)), 32);
    const t = new SigningContext('SchnorrRistrettoHDKD');
    t.bytes(EMPTY);
    t.appendMessage('chain-code', chainCode);
    t.appendMessage('secret-key', key);
    const msk = t.challengeBytes('HDKD-hard', 32);
    const hdkdChainCode = t.challengeBytes('HDKD-chaincode', 32);
    t.clean();
    const res = secretFromSeed(msk);
    cleanBytes(key, msk, hdkdChainCode);
    t.clean();
    return res;
  },
});
// Schnorr DLEQ
// Follow the kusama/schnorrkel VRF transcript order: commit `vrf:pk` after `vrf:h^r`.
type Proof = { s: bigint; c: bigint };
const dleq = /* @__PURE__ */ (() => ({
  proove(
    keyScalar: bigint,
    nonce: TArg<Uint8Array>,
    pubPoint: Point,
    t: TArg<SigningContext>,
    input: Point,
    output: Point,
    random: TArg<Uint8Array>
  ) {
    const tx = t as SigningContext;
    const ns = nonce as Uint8Array;
    const rnd = random as Uint8Array;
    tx.protoName('DLEQProof');
    tx.commitPoint('vrf:h', input);
    const r = tx.witnessScalar(`proving${'\0'}0`, rnd, [ns]);
    const R = RistrettoPoint.BASE.multiply(r);
    tx.commitPoint('vrf:R=g^r', R);
    const Hr = input.multiply(r);
    tx.commitPoint('vrf:h^r', Hr);
    tx.commitPoint('vrf:pk', pubPoint);
    tx.commitPoint('vrf:h^sk', output);
    const c = tx.challengeScalar('prove');
    const s = modN(r - c * keyScalar);
    return { proof: { c, s } as Proof, proofBatchable: { R, Hr, s } };
  },
  verify(pubPoint: Point, t: TArg<SigningContext>, input: Point, output: Point, proof: Proof) {
    const tx = t as SigningContext;
    if (pubPoint.equals(RistrettoPoint.ZERO)) return false;
    tx.protoName('DLEQProof');
    tx.commitPoint('vrf:h', input);
    const R = pubPoint.multiply(proof.c).add(RistrettoPoint.BASE.multiply(proof.s));
    tx.commitPoint('vrf:R=g^r', R);
    const Hr = output.multiply(proof.c).add(input.multiply(proof.s));
    tx.commitPoint('vrf:h^r', Hr);
    tx.commitPoint('vrf:pk', pubPoint);
    tx.commitPoint('vrf:h^sk', output);
    const realC = tx.challengeScalar('prove');
    if (proof.c === realC) return { R, Hr, s: proof.s }; // proofBatchable
    return false;
  },
}))();

// VRF: Verifiable Random Function
function initVRF(
  ctx: TArg<Uint8Array>,
  msg: TArg<Uint8Array>,
  extra: TArg<Uint8Array>,
  pubPoint: Point
) {
  const t = new SigningContext('SigningContext');
  t.label(ctx);
  t.bytes(msg);
  t.commitPoint('vrf-nm-pk', pubPoint);
  const hash = t.challengeBytes('VRFHash', 64);
  const input = ristretto255_hasher.deriveToCurve!(hash);
  // Hash the input on the SigningContext transcript, then start DLEQ on a fresh `VRF`
  // transcript like schnorrkel.
  const transcript = new SigningContext('VRF');
  // Extra bytes bind only the separate DLEQ transcript; they do not change the hashed
  // VRF input point.
  if (extra.length) transcript.label(extra);
  t.clean();
  cleanBytes(hash);
  return { input, t: transcript };
}
type VRF = {
  sign(
    msg: Uint8Array,
    secretKey: Uint8Array,
    ctx: Uint8Array,
    extra: Uint8Array,
    random?: Uint8Array
  ): Uint8Array;
  verify(
    msg: Uint8Array,
    signature: Uint8Array,
    publicKey: Uint8Array,
    ctx?: Uint8Array,
    extra?: Uint8Array
  ): boolean;
};
/**
 * Verifiable random function helpers built on sr25519.
 * @example
 * Generate and verify a VRF proof for the message.
 * ```ts
 * import { getPublicKey, secretFromSeed, vrf } from '@scure/sr25519';
 * import { randomBytes } from '@noble/hashes/utils.js';
 * const secretKey = secretFromSeed(randomBytes(32));
 * const msg = new Uint8Array([1, 2, 3]);
 * const sig = vrf.sign(msg, secretKey);
 * vrf.verify(msg, sig, getPublicKey(secretKey));
 * ```
 */
export const vrf: TRet<VRF> = /* @__PURE__ */ Object.freeze({
  sign(msg, secretKey, ctx = EMPTY, extra = EMPTY, random = randomBytes(32)) {
    abytes('msg', msg);
    abytes('secretKey', secretKey, 64);
    abytes('ctx', ctx);
    abytes('extra', extra);
    const keyScalar = decodeScalar(secretKey.subarray(0, 32));
    // Copy the nonce seed before witness generation so cleanup does not zeroize
    // the caller's secretKey buffer.
    const nonce = Uint8Array.from(secretKey.subarray(32, 64));
    const pubPoint = RistrettoPoint.fromBytes(getPublicKey(secretKey));
    const { input, t } = initVRF(ctx, msg, extra, pubPoint);
    const output = input.multiply(keyScalar);
    const p = { input, output };
    const { proof } = dleq.proove(keyScalar, nonce, pubPoint, t, input, output, random);
    const cBytes = numberToBytesLE(proof.c, 32);
    const sBytes = numberToBytesLE(proof.s, 32);
    const res = concatBytes(p.output.toBytes(), cBytes, sBytes);
    cleanBytes(nonce, cBytes, sBytes);
    return res;
  },
  verify(msg, signature, publicKey, ctx = EMPTY, extra = EMPTY): boolean {
    abytes('msg', msg);
    abytes('signature', signature, 96); // O(point) || c(scalar) || s(scalar)
    abytes('pubkey', publicKey, 32);
    abytes('ctx', ctx);
    abytes('extra', extra);
    const pubPoint = RistrettoPoint.fromBytes(publicKey);
    if (pubPoint.equals(RistrettoPoint.ZERO)) return false;
    const proof: Proof = {
      c: parseScalar('signature.c', signature.subarray(32, 64)),
      s: parseScalar('signature.s', signature.subarray(64, 96)),
    };
    const { input, t } = initVRF(ctx, msg, extra, pubPoint);
    const output = RistrettoPoint.fromBytes(signature.subarray(0, 32));
    if (output.equals(RistrettoPoint.ZERO))
      throw new Error('vrf.verify: wrong output point (identity)');
    const proofBatchable = dleq.verify(pubPoint, t, input, output, proof);
    return proofBatchable === false ? false : true;
  },
});

// NOTE: for tests only, don't use
export const __tests: {
  Strobe128: typeof Strobe128;
  Merlin: typeof Merlin;
  SigningContext: typeof SigningContext;
} = /* @__PURE__ */ Object.freeze({
  Strobe128,
  Merlin,
  SigningContext,
});

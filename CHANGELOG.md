# Changelog for scure-sr25519

## 2.3.0 (2026-08-08)

Improve error messages and type checks. Upgrade noble-hashes and noble-curves to 2.3.0.

## 2.2.0 (2026-04-22)

* **April 2026 self-audit** (all files): no major issues found
  * Audited for spec compliance and security
  * Minor hardening all over the place
  * Ensure `sign` does not mutate secret key input array
  * `fromKeypair` now decodes secret key in line with `paritytech/schnorrkel` library. It forces scalar to be torsion-free (`% cofactor === 0`). Check out diff for more details
* Fix all Byte Array types, to ensure proper work in both TypeScript 5.6 & TypeScript 5.9+
  * TS 5.6 has `Uint8Array`, while TS 5.9+ made it generic `Uint8Array<ArrayBuffer>`
  * This creates incompatibility of code between versions
  * Previously, it was hard to use and constantly emitted errors similar to `TS2345`
  * See [typescript#62240](https://github.com/microsoft/TypeScript/issues/62240) for more context
* Fix compilation issues on TypeScript v6
* Improve tree-shaking, reduce bundle sizes
* Upgrade noble-curves and noble-hashes to self-audited v2.2

*(Version is bumped from v1.0 to v2.2, to align with other noble / scure packages)*

## 1.0.0 (2025-12-08)

- No code changes from v0.3: bumping to v1 to signify stability
- NPM: Switch to token-less Trusted Publishing, enable provenance

## 0.1.0 (2024-11-23)

- Initial release

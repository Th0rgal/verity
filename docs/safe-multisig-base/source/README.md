# Safe Multisig Base Source Snapshot

This directory contains a pinned snapshot of the Safe base contract source
used for the formal proof work in this repo.

## Upstream Pin
- Repo: safe-fndn/safe-smart-account
- Release tag: v1.5.0
- Commit: dc437e8
- Contract: contracts/Safe.sol (Safe)
- Interface: contracts/interfaces/ISafe.sol (ISafe)
- Retrieved: 2026-02-12

## Integrity
- SHA256 (Safe.sol): `4b54dce0ad9d9c1264ecd5c146c82b7bc17d24f981bd42525487be3bf6a40366`
- Detached hash file: `Safe.sol.sha256`
- SHA256 (base/OwnerManager.sol): `cb5f04371f1918129d9b175bde7f346376b53cdcc94e67f427bccea6e2659a6a`
- SHA256 (base/ModuleManager.sol): `db2d5776c421b2613ec3f9881716d7c64c993e1cdd1ad83c213a2c32c1208dd2`
- SHA256 (base/GuardManager.sol): `7560378f976c2a7dc655db11d387a83f69943bf249cc74faca343bc72de60e73`
- SHA256 (base/FallbackManager.sol): `fe990479ee73d9f0f602ec1a79f7c34b9fb6875b51d879d5929a3d6344f5e111`
- SHA256 (common/Singleton.sol): `dd6e1eb6292caa256bcbc953a7f64ec26d3262c4b9e6893e002f0c602ec1985d`
- SHA256 (interfaces/ISafe.sol): `ee9949b44f6b21f078e6b69dd927107f233fc38c1ea5b6d46b4618bf3a8af04d`
- Detached hash file: `interfaces/ISafe.sol.sha256`

## Notes
- This is a verbatim copy of the upstream contract file at the pinned commit.
- Any modifications for EDSL equivalence should be done in the EDSL, not here.

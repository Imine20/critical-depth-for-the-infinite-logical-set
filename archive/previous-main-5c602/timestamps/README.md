# Timestamp evidence for the primary release

Both mechanisms bind the exact bytes of `timestamps/release-manifest.txt`:

- Length: **8,278 bytes**.
- SHA-256: **a3e283cc6e07c705e8d181a54cdbda4e01f3e2ecb873d15b63ad9cba60f8a2a8**.
- Coverage: the 76 primary files listed in that manifest, including the selected TeX/PDF, Lean sources, documentation and verification evidence.
- Primary code commit: [`e882b1bd36838b3f825d35f07d9d4b46a5d3357b`](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/commit/e882b1bd36838b3f825d35f07d9d4b46a5d3357b); tree `de2c48569f722af69ee92b2031a1aeba26d9cd3f`.

The manifest excludes itself and subsequent timestamp receipts to avoid self-reference. Its rows contain SHA-256, byte length and repository-relative path, separated by tabs. Later file revisions require a new manifest and new timestamps.

Current status: **RFC 3161 verified; OpenTimestamps calendar-pending.** The initial OTS receipt contains three real pending calendar attestations. Bitcoin confirmation has not yet been established in this note; any later confirmation must identify the upgraded receipt, block height and verification method.

## Check the collection

Run from a byte-preserving Linux checkout at the repository root. Line-ending conversion changes file hashes. Check the receipt files with `sha256sum -c timestamps/receipts.sha256`, then run the collection checks below with `sha256sum` and `awk`:

```sh
printf '%s  %s\n' \
  a3e283cc6e07c705e8d181a54cdbda4e01f3e2ecb873d15b63ad9cba60f8a2a8 \
  timestamps/release-manifest.txt | sha256sum -c -
wc -c < timestamps/release-manifest.txt
awk -F '\t' '!/^#/ && NF == 3 { print $1 "  " $3 }' \
  timestamps/release-manifest.txt | sha256sum -c -
```

The length must be 8278 and every file check must succeed. These checks bind the stamped manifest to the available collection; the proof replay instructions remain in `docs/VERIFICATION.md`.

## RFC 3161

The preserved request and first response are `rfc3161/release-manifest.tsq` and `rfc3161/release-manifest.tsr`, relative to this directory. There was one TSA POST. Verification resumed locally against that same response after an OpenSSL filename-list issue; no second TSA request was made.

The response was granted. Both OpenSSL timestamp verifications returned `Verification: OK`; separate certificate-chain verification with purpose `timestampsign` also succeeded. The actual signer has the exclusive, critical Time Stamping extended key usage.

| Signed response field | Value |
| --- | --- |
| TSA `genTime` | 2026-11-01T09:05:03Z |
| Policy | `2.16.840.1.114412.7.1` |
| Serial | `FF0441FAADC17AC48716290B57C17DA9` |
| Signer | DigiCert SHA256 RSA4096 Timestamp Responder 2026 1 |
| Signer certificate SHA-256 | `2DA09DA7F4131F9FE72DB6C5E6E9C9656755AF043F1EA742CC0D2120E141EBFC` |
| Issuer | DigiCert Trusted G4 TimeStamping RSA4096 SHA256 2025 CA1 |
| Trust anchor | DigiCert Trusted Root G4 |

The root's DER SHA-256 fingerprint is:

```text
552F7BDCF1A7AF9E6CE672017F4F12ABF77240C78E761AC203D1D9D20AC89988
```

Its serial is `059B1B579E8E2132E23907BDA777755C`; its validity runs from 2013-08-01 to 2038-01-15. The verification used an existing distribution-provided OS certificate, with package provenance and the published fingerprint checked. For independent replay, confirm `trusted-root.pem` against your genuine OS trust store or DigiCert's authenticated [root-certificate metadata](https://knowledge.digicert.com/general-information/digicert-trusted-root-authority-certificates). A certificate supplied alongside a receipt becomes a trust anchor only after that independent confirmation. DigiCert also publishes the [root certificate](https://knowledge.digicert.com/content/dam/kb/attachments/time-stamp/DigiCertTrustedRootG4.cer) and [TSA endpoint and rotating certificate information](https://knowledge.digicert.com/general-information/rfc3161-compliant-time-stamp-authority-server).

From the repository root, use relative basenames as follows. OpenSSL's `ts -untrusted` option can split a filename containing spaces internally, even when the shell quoted it; changing directory avoids that issue.

```sh
cd timestamps/rfc3161
openssl x509 -in trusted-root.pem -outform DER | openssl dgst -sha256
openssl ts -query -in release-manifest.tsq -text
openssl ts -reply -in release-manifest.tsr -text
openssl ts -verify -in release-manifest.tsr \
  -queryfile release-manifest.tsq \
  -CAfile trusted-root.pem -untrusted response-certificates.pem
openssl ts -verify -in release-manifest.tsr \
  -data ../release-manifest.txt \
  -CAfile trusted-root.pem -untrusted response-certificates.pem
openssl verify -show_chain -purpose timestampsign \
  -CAfile trusted-root.pem -untrusted response-certificates.pem actual-signer.pem
openssl x509 -in actual-signer.pem -noout \
  -subject -issuer -serial -dates -fingerprint -sha256 -ext extendedKeyUsage
cd ../..
```

Require successful exits for all verification commands, `Verification: OK` for both `ts` commands, and `actual-signer.pem: OK` for the chain check. The query verification checks the saved request, including its fresh nonce and SHA-256 imprint; the data verification checks the canonical manifest bytes. Inspect the signer fingerprint and the exclusive critical Time Stamping EKU. Saved portable evidence includes `query.txt`, `reply.txt`, `verify-query.txt`, `verify-file.txt` and `signer-EKU.txt` in `timestamps/rfc3161/`.

The response certificate bundle contains both the signer and its issuer. OpenSSL may warn that the signer in the untrusted stack is not a CA; the separate purpose/chain and timestamp checks above still returned OK. This warning is retained rather than presented as a warning-free run.

**Revocation was not checked.** These results establish the observed signature, usage, chain and byte/request binding under the stated trust anchor. They do not provide a CRL/OCSP-backed or indefinite long-term validation claim. See the [OpenSSL timestamp verification documentation](https://docs.openssl.org/3.0/man1/openssl-ts/).

## OpenTimestamps

The initial receipt `ots/release-manifest.txt.ots` is preserved unchanged: 794 bytes, SHA-256 `28ae737b9fbffbbd3518f9677e96220b97eb2e9c7e5ff59e884bf5717bc50824`.

The preserved upgrade copy `ots/release-manifest.txt.upgrade.ots` was checked at controller time 2026-11-01T09:12:39.219Z. Its bytes remain identical to the initial receipt. Bob and Finney reported pending Bitcoin confirmation; Alice's query failed with an AggregateError. No Bitcoin block-header attestation was returned, and no public explorer was contacted. The initial receipt remains unchanged. The structured outcomes are in [verification.json](verification.json).
Its independently checked file digest matches the manifest. Three parsed pending attestations name:

- `alice.btc.calendar.opentimestamps.org`
- `bob.btc.calendar.opentimestamps.org`
- `finney.calendar.eternitywall.com`

The requests used the selected HTTPS calendar pools `https://a.pool.opentimestamps.org`, `https://b.pool.opentimestamps.org` and `https://a.pool.eternitywall.com`. The inspected official JavaScript client added a fresh 16-byte nonce before submitting its SHA-256 commitment. Three actual parsed responses were counted; the client's `-m` option or exit status alone was not treated as evidence. The receipt records the actual responding calendar identities above.

The [official JavaScript client](https://github.com/opentimestamps/javascript-opentimestamps) is published as npm package `opentimestamps`; the client used here was **0.4.9**. With Node.js and npm available, these commands install that package version into a separate local tool directory and inspect the original receipt. They do not submit a new stamp:

```sh
mkdir -p .timestamp-client
cp timestamps/client-package.json .timestamp-client/package.json
cp timestamps/client-lock.json .timestamp-client/package-lock.json
npm ci --prefix .timestamp-client --cache .timestamp-client/npm-cache \
  --ignore-scripts --no-audit --no-fund
OTS_CLI=.timestamp-client/node_modules/opentimestamps/ots-cli.js
node "$OTS_CLI" info timestamps/ots/release-manifest.txt.ots
```

Check the reported file SHA-256 against the manifest digest above. A `PendingAttestation` records calendar acceptance; it does not establish a confirmed Bitcoin block.

Upgrade a new copy, preserving the initial receipt. These later commands contact the receipt's calendars; Bitcoin verification may also query public blockchain services depending on the client's configuration.

```sh
set -eu
OTS_UPGRADE=timestamps/ots/release-manifest.upgrade-$(date -u +%Y%m%dT%H%M%SZ).txt.ots
test ! -e "$OTS_UPGRADE"
cp timestamps/ots/release-manifest.txt.ots "$OTS_UPGRADE"
node "$OTS_CLI" upgrade "$OTS_UPGRADE"
node "$OTS_CLI" info "$OTS_UPGRADE"
node "$OTS_CLI" verify -f timestamps/release-manifest.txt "$OTS_UPGRADE"
```

The shell error handling stops if the destination already exists. Retain the initial receipt even after an upgrade succeeds. Claim Bitcoin confirmation only after the upgraded proof contains a valid Bitcoin block-header attestation and verification succeeds against the same manifest. Record the upgraded receipt's SHA-256, block height and whether verification used a local Bitcoin node or an explorer. Until then, leave the status calendar-pending.

## Distinct recorded clocks and scope

All values below use UTC, with their clock source stated:

| Event | Recorded time | Clock source |
| --- | --- | --- |
| Primary code commit committer field | 2026-11-01T09:04:32Z | GitHub commit metadata |
| Signed RFC 3161 `genTime` | 2026-11-01T09:05:03Z | TSA |
| TSA request observation | 2026-11-01T09:09:43Z | Task controller |
| Initial three-calendar OTS receipt observation | 2026-11-01T09:09:52Z | Task controller |
| Successful RFC 3161 verification observation | 2026-11-01T09:10:59Z | Task controller |

These clocks were not calibrated against one another. The signed TSA value and controller observations are reported separately; no alignment or cross-clock ordering claim is inferred from them.

The timestamps concern existence of the exact manifest bytes and, through its hashes, the listed collection. They do not establish authorship, originality, legal qualification or mathematical correctness. Lean proof acceptance and the remaining author semantic review are documented separately.

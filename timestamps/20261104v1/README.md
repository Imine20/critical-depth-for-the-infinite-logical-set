# RFC 3161 timestamp for 20261104v1.tex

The signed token records 2026-11-04 02:37:04 UTC, which is 2026-11-04 10:37:04 in Asia/Shanghai. The saved request, nonce, SHA-256 imprint, TSA signature, timestamping certificate usage and certificate chain all passed verification.

## Frozen manuscript

- File [20261104v1.tex](../../manuscript/20261104v1.tex)
- Exact byte length 43,033
- SHA-256 `7777ecaefbaf8891090754c6cdb884e49f57c9d3bdd2a29c7451da120b9c860d`
- Git blob `0f377da56b24d4728b435d3453b1a19659898234`
- Initial publication commit [1e994a10da4040dfbe8d6937fba1bac96a87548a](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/commit/1e994a10da4040dfbe8d6937fba1bac96a87548a)

The manuscript was copied without byte changes. An anonymous download from its immutable public commit had the same SHA-256 before the timestamp request was sent.

## Signed receipt

- TSA endpoint `http://timestamp.digicert.com`
- Protocol RFC 3161
- Status Granted
- Policy OID `2.16.840.1.114412.7.1`
- Token serial `0xF861F4E61EDDFF5A76032431249F901A`
- Request and response nonce `0x1FD3E74A7C6BCFE6`
- Actual signer DigiCert SHA256 RSA4096 Timestamp Responder 2026 1
- Signer SHA-256 `2da09da7f4131f9fe72db6c5e6e9c9656755af043f1ea742cc0d2120e141ebfc`

The request contained the SHA-256 imprint, a random nonce and a certificate-request flag. The endpoint uses HTTP. The signed response was verified independently of the transport.

## Trust and verification

The self-signed DigiCert Trusted Root G4 certificate was exported from the Windows LocalMachine trusted root store, thumbprint `DDFB16CD4931C973A2037D3FC83A4D7D775D05E4`. Its DER SHA-256 is `552f7bdcf1a7af9e6ce672017f4f12abf77240c78e761ac203d1d9d20ac89988`, cross-checked against DigiCert's official root documentation. The response supplied the intermediate certificate. The signer has critical Time Stamping extended key usage.

From this directory in a checkout, run the following commands with OpenSSL.

~~~sh
openssl verify -purpose timestampsign -CAfile digicert-trusted-root-g4.pem -untrusted issuer-intermediate.pem actual-signer.pem
openssl ts -verify -queryfile 20261104v1.tex.tsq -in 20261104v1.tex.tsr -CAfile digicert-trusted-root-g4.pem -untrusted issuer-intermediate.pem
openssl ts -verify -data ../../manuscript/20261104v1.tex -in 20261104v1.tex.tsr -CAfile digicert-trusted-root-g4.pem -untrusted issuer-intermediate.pem
sha256sum --check SHA256SUMS.txt
~~~

The signer-chain check returned OK. Both timestamp verification commands returned `Verification: OK`. The saved request binds the nonce as well as the imprint. Certificate revocation status was not checked. Verification used OpenSSL 3.2.4.

OpenTimestamps remains suspended at the user's request. This evidence concerns the exact TeX bytes. The repository's historical Lean verification records identify their own source versions.

## Evidence files

[RECEIPT.json](RECEIPT.json) records identifiers, hashes and verification results. [query.txt](query.txt), [reply.txt](reply.txt) and [verification.txt](verification.txt) contain the request, response and verification output. The binary .tsq and .tsr files are preserved as generated and received.

DigiCert documents the [TSA endpoint and rotating certificate chain](https://knowledge.digicert.com/general-information/rfc3161-compliant-time-stamp-authority-server) and [trusted root fingerprints](https://knowledge.digicert.com/general-information/digicert-trusted-root-authority-certificates).


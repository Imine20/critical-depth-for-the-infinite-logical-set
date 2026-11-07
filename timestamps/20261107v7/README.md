# RFC 3161 timestamps for the v7 manuscript

The DigiCert receipts bind the exact [published TeX](../../manuscript/20261107v7.tex) and [PDF](../../manuscript/20261107v7.pdf). The files first appeared in this branch at [2b83c52](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/commit/2b83c5232fb35ec4bf42a5f004a4ac875e5a71e9). Public downloads from that commit matched the supplied bytes before the requests were sent.

| File | SHA-256 | Signed time in UTC |
| --- | --- | --- |
| 20261107v7.tex | 70c261a982af5cbf4bb6a8784f5996a6d1ca9bf7ab34cc8b3ed5034a42adf271 | Nov 7 03:11:10 2026 GMT |
| 20261107v7.pdf | ca3010f710a50fa394d40c651fdd5a5828e05b2871e9824e262236a0623f3137 | Nov 7 03:11:11 2026 GMT |

The [machine receipt](RECEIPT.json) records the issuer, signer EKU, policy, serial, nonce, request and response hashes. The server endpoint is documented by [DigiCert](https://knowledge.digicert.com/general-information/rfc3161-compliant-time-stamp-authority-server). The timestamp request carried a SHA-256 imprint, a fresh nonce and the certificate request flag.

## Verify locally

From this directory, run both checks for each file.

~~~sh
for file in 20261107v7.tex 20261107v7.pdf; do
  openssl ts -verify -queryfile "$file.tsq" -in "$file.tsr" \
    -CAfile digicert-trusted-root-g4.pem -untrusted issuer-intermediate.pem
  openssl ts -verify -data "../../manuscript/$file" -in "$file.tsr" \
    -CAfile digicert-trusted-root-g4.pem -untrusted issuer-intermediate.pem
done
~~~

Each command returned Verification: OK with OpenSSL 3.2.4. The first check binds the token to the saved request and nonce. The second checks the exact manuscript bytes. The token signer has the critical Time Stamping extended key usage and chains to the self-signed DigiCert Trusted Root G4 exported from the local Windows trust store. Its DER SHA-256 is 552f7bdcf1a7af9e6ce672017f4f12abf77240c78e761ac203d1d9d20ac89988. Independently compare that root with a trusted certificate source when reproducing the verification. Revocation status was outside this verification. The user requested the RFC 3161 workflow under the OpenTimestamps suspension.

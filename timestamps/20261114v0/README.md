# RFC 3161 timestamp for 20261114v0.tex

This receipt binds the 115,166 bytes in [the TeX manuscript](../../manuscript/20261114v0.tex).
The SHA-256 digest is DE0A9890B6BEC7EB82BF55F8467339538E799B064ECC2A19B695F41D4236C975.

DigiCert issued the token on 2026-11-14 at 07:58:18 UTC. The response reports
Granted. The policy OID is 2.16.840.1.114412.7.1 and the serial number is
68699E680E7D0A2DC9BD5CD94063BC7D (hex). The request carried a SHA-256
imprint, a fresh nonce and the certificate request flag. The original DER
request and response are included alongside their decoded fields.

The signer certificate has the critical timeStamping extended key usage.
The certificate chain terminates at the self-signed DigiCert Trusted Root G4.
Its DER SHA-256 fingerprint is
552F7BDCF1A7AF9E6CE672017F4F12ABF77240C78E761AC203D1D9D20AC89988.
Cross-check this fingerprint against an independently trusted source before
using the bundled root. The certificate material and issuer links are
documented by [DigiCert](https://knowledge.digicert.com/general-information/rfc3161-compliant-time-stamp-authority-server).
The same root fingerprint is listed in [Apple's trust store documentation](https://support.apple.com/en-am/103243).

Run the following commands from this evidence directory. The first checks
the saved request and its nonce. The second checks the manuscript bytes.

    openssl ts -verify -queryfile 20261114v0.tex.tsq -in 20261114v0.tex.tsr -CAfile trusted-root.pem -untrusted intermediate.pem
    openssl ts -verify -data ../../manuscript/20261114v0.tex -in 20261114v0.tex.tsr -CAfile trusted-root.pem -untrusted intermediate.pem

Both commands returned Verification: OK with OpenSSL 3.2.4. The
certificate revocation lists came from the distribution points in the signer
and intermediate certificates. OpenSSL validated the signed CRLs and checked
the chain at genTime and again at the verification time.

    openssl verify -purpose timestampsign -attime 1794643098 -crl_check_all -CRLfile digicert-crls.pem -CAfile trusted-root.pem -untrusted intermediate.pem 20261114v0.tex.signer.pem

The receipt records when the TeX bytes existed, subject to trust in the
time-stamping authority and its clock. OpenTimestamps was omitted at the
author's request.

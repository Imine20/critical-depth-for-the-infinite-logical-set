# Current release timestamp receipts

The frozen [release-manifest.txt](release-manifest.txt) contains the SHA-256,
byte length and repository-relative path of 57 current files. Its exact
6,735 bytes have SHA-256
dee22d1fb2fbc9f25583321df7185bbe07521417dbea03d9f9b52f90cd5240cf.
It includes the integrated Lean source, actual execution evidence, latest
user-provided TeX/PDF, reference manuscript and explanatory documents.
This timestamp directory and subsequent Git metadata are outside that collection.

**RFC 3161: verified signature, nonce, imprint and certificate chain.**
DigiCert signed the manifest digest at **2026-11-01 17:17:40 UTC**, serial
EC5002D8BC64DD59F80252B145DB602C. The unchanged request and response are in
[rfc3161](rfc3161/). Verification used a preexisting distribution-installed
DigiCert Trusted Root G4, its independently checked DER fingerprint, the OS CA
store, and the response certificates as untrusted intermediates. The signer's
critical EKU contains only Time Stamping. Both the request/nonce and actual
manifest-byte verification succeeded. CMS extraction alone was not acceptance.
OCSP/CRL revocation status is **UNCHECKED**.

The controller recorded request/response times 17:22:19–17:22:20 UTC, about
279–280 seconds later than the signed TSA clock. The clocks are kept distinct;
no synchronization audit or cause attribution is claimed.

**OpenTimestamps: three valid calendar replies; Bitcoin confirmation PENDING.**
The immutable [initial receipt](release-manifest.txt.ots) is 737 bytes,
SHA-256 f803ed4d9c12bbb9671a6dcc8969128faf45600ad545172917ea3c3da826779a.
Actual parsed responses came from Bob, Finney and Catallaxy, carrying three
different pending calendar URIs. Alice did not reply successfully. The required
minimum is two actual parsed replies; the helper counted replies rather than
trusting the client API's m parameter. This is not a claim of independent
calendar operators.

One bounded upgrade attempt still reported pending and is preserved as
[an upgrade copy](ots/release-manifest.txt.upgrade.ots), with the initial receipt
unchanged. No Bitcoin attestation, block height or confirmed timestamp is
claimed. The earlier attempt obtained only one reply; its
[289-byte receipt](ots/first-attempt-single-calendar.ots) is retained as an
unsuccessful threshold attempt.

The public client was JavaScript OpenTimestamps 0.4.9, commit
36e27fca500273a63e013fff62d963357e882a27. Its official nonce construction
blinds the 32-byte digest with a fresh 16-byte nonce before calendar submission.
No article bytes or filenames were sent. Alternative endpoints follow the
[official calendar list](https://opentimestamps.org/#calendars) and the pinned
client's defaults. [RECEIPTS.json](RECEIPTS.json) records actual selected
endpoints, parsed replies, statuses and hashes.

From the repository root, verify the proof/evidence file identities:

~~~sh
sha256sum -c verification-runs/20261102-3c90628/SHA256SUMS.txt
cd timestamps/20261102-current
sha256sum -c SHA256SUMS.txt
openssl ts -verify -queryfile rfc3161/release-manifest.tsq \
  -in rfc3161/release-manifest.tsr \
  -CAfile rfc3161/trusted-root.pem \
  -untrusted rfc3161/response-certificates.pem
openssl ts -verify -data release-manifest.txt \
  -in rfc3161/release-manifest.tsr \
  -CAfile rfc3161/trusted-root.pem \
  -untrusted rfc3161/response-certificates.pem
openssl x509 -in rfc3161/actual-signer.pem -noout -ext extendedKeyUsage
~~~

These commands perform certificate checks at the verifier's current time;
future expiry and historical revocation assessment require separate handling.
With the official OpenTimestamps CLI, the following command inspects the
published proof:

~~~sh
ots info release-manifest.txt.ots
~~~

In a separate copy of this directory, run:

~~~sh
ots upgrade release-manifest.txt.ots
ots verify release-manifest.txt.ots
~~~

A pending result is not Bitcoin verification. A timestamp binds file bytes;
it does not prove the mathematics or authorship, and does not change author
semantic approval from **PENDING** or the deferred status of the manuscript's
CAD proof. The current Lean source passed its separately documented compilation
and recursive axiom audit.

# ACL2 books

The release books are intended to certify conventionally under ACL2 8.7 after their community-book dependencies are available.

Run from the repository root:

```sh
ACL2=/path/to/saved_acl2 sh scripts/certify-all.sh
```

Certification success is checked by actual `.cert` creation rather than shell exit status alone.

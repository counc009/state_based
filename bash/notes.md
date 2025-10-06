# Natural Language Description
Print the number of lines in the file 'bigfile' to stderr and gzip 'bigfile' to 'bigfile.gz'

# Bash Scripts
## The fun one
```bash
tee >(wc -l >&2) < bigfile | gzip > bigfile.gz
```

## The normal one
```bash
wc -l bigfile >&2
gzip -k bigfile
```

## The cat one
```bash
cat bigfile | gzip > bigfile.gz
cat bigfile | wc -l >&2
```

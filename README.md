# Matmod: Verify Relevance Properties for Matrix Models with Implicative Connectives

Interested in seeing which satisfiable models from [arranstewart/magic](https://github.com/arranstewart/magic) have the variable sharing property?

(1) Generate satisfiable matrix models using `magic`.
 - Use the `ugly` data format as the output
 - Keep in mind not all logic features in magic are supported, check out the [GitHub issue tracker](https://github.com/Brandon-Rozek/matmod/issues) to see upcoming features or make your own requests

(2) Run our tool! It will first attempt to parse all the matrices in the output file and then check for the variable sharing property one-by-one.

```
python3 parse_magic.py < UGLY_FILE_FROM_MAGIC
```

If you face any troubles, feel free to reach out. This tool also has capabilities to generate satisfiable models given a specification (see: R.py), however, it is much slower than magic so you're better off using that.


# VSPursuer: Verify Relevance Properties for Matrix Models with Implicative Connectives

Interested in seeing which satisfiable models from [arranstewart/magic](https://github.com/arranstewart/magic) have the variable sharing property?

(1) Generate satisfiable matrix models using `MaGIC`.
 - Use the `ugly` data format as the output

(2) Run our tool! It will first attempt to parse all the matrices in the output file and then check for the variable sharing property one-by-one.

```
./vspursuer.py -i examples/R6
```

If you face any troubles, feel free to reach out. This tool also is able to generate satisfiable models given a specification (see: R.py). This is, however, much slower than MaGIC so you're better off using that.

Check out the [GitHub issue tracker](https://github.com/Brandon-Rozek/matmod/issues) to see upcoming features or make your own requests.

This is a compiler from Simply-Typed Lambda Calculus to System F that performs closure conversion. It uses the [locally nameless representation](http://www.chargueraud.org/research/2009/ln/main.pdf) of variable bindings.

- For the original paper on closure conversion, see [Typed Closure Conversion](http://www.cs.cmu.edu/~rwh/papers/closures/popl96.pdf).
- The translation used is from [Perconti and Ahmed](http://www.ccs.neu.edu/home/amal/papers/voc-tr.pdf), which in turn is based on [From System F to Typed Assembly Language](https://www.cs.princeton.edu/~dpw/papers/tal-toplas.pdf).
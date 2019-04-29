ssr-under-tac
=============

This repository gathers a Coq theory [under.v](src/under.v) providing
a tactic (implemented in pure Ltac) to easily rewrite under lambdas
within the SSReflect/MathComp library.

> **NOTE: This GitHub repository is not maintained anymore**.
> 
> Please consider using the new implementation of the `under` tactic,
> which has been reimplemented from scratch jointly with Enrico Tassi
> in [PR coq/coq#9651](https://github.com/coq/coq/pull/9651).

Compatibility
-------------

The `master` branch of this repo had been tested with Coq 8.5(pl2) and
[math-comp 3b97308](https://github.com/math-comp/math-comp/tree/3b97308b6314e34d78a6f14c8173956aa64bd026).

Usage
-----

* `under [ssrpattern] eq_lemma [intropattern] tactic.`  
  or simply   
* `under eq_lemma [intropattern] tactic.`  

Examples
--------
* `under [X in _ = X + _ + _] eq_bigr [i Hi] rewrite GRing.mulrDl.`  
* `under eq_bigr ? under eq_bigl ? rewrite setIT.`   

For more examples, see the [examples.v](src/examples.v) file.

Author
------

* Erik Martin-Dorel

This tactic was also the result of discussions with:

* Pierre Roux
* Cyril Cohen

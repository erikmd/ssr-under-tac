ssr-under-tac
=============

This repository gathers a Coq theory [under.v](src/under.v) providing
several tactics to easily rewrite under lambdas within the
SSReflect/MathComp library.

Usage
-----

* `under [ssrpattern] eq_lemma [intropattern] tactic.`  
  or simply   
* `under eq_lemma [intropattern] tactic.`  

Examples
--------
* `under [X in _ = X + _ + _] eq_bigr [i Hi] rewrite GRing.mulrDl.`  
* `under eq_bigr ? under eq_bigl ? rewrite setIT.`   

For more examples, see the [examples.v](examples/examples.v) file.

Author
------

* Erik Martin-Dorel

This tactic was also the result of discussions with:

* Pierre Roux
* Cyril Cohen

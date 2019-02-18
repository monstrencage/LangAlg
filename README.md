# LangAlg
A complete axiomatization of the algebra of languages over the signature of reversible Kleene lattices, proved in Coq.

### What is this repository for? ###

This repository contains the full proof.
The documentation is also available on my personal webapge, [here](http://paul.brunet-zamansky.fr/languages.html).

### How do I get set up? ###

This proof was developped using [Coq](coq.inria.fr) version 8.8.1.
To download the proof, simply run the command:
``` shell
git clone git@github.com:monstrencage/LangAlg.git
```
We generated a `Makefile` automatically using the tool `coq_makefile`. 
The documentation for this tool can be found [here](https://coq.inria.fr/refman/Reference-Manual017.html#Makefile).
To generate the `Makefile`, run the command:
``` shell
coq_makefile -f _CoqProject -o Makefile
```
Then the proof can be compiled and its documentation generated by calling:
``` shell
make gallinahtml
```

For readability reasons, we heavily use utf-8 symbols. To navigate the proof, we recommend using [emacs](https://www.gnu.org/software/emacs/) with [Proof General](https://proofgeneral.github.io/) and [company-coq](https://melpa.org/#/company-coq).

### Overview of the proof ###

* **tools**
Toolbox of simple definitions, lemmas and tactics.

* **language**
Basics of languages.

* **prime_set**
Simple facts about sets obtained by duplication.

* **klm**
Identity-free Kleene lattices

* **one_free_expr**
Expressions without the constant 1

* **lklc**
Definition and equational theory of reversible Kleene lattices.

* **lklc_lang**
Language interpretation of expressions from lklc.

* **lklc_reduction**
Important intermediary steps towards a reduction from lklc to one_free_expr.

* **completeness**
We finally arrive to the main result of this development: the proof that our axiomatization is complete for the equational theory of languages.

* **top**
Some facts about adding the constant top to the signature.
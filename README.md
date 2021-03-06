## Machine Checked Proofs of Real-or-random Secrecy and Authentication using Computationally Complete Symbolic Attacker (CCSA)

We formalized the proofs of real-or-random secrecy and authentication properties of the Diffie-Hellman (DH) and the Station-to-Station (STS) protocol respectively in the [Coq proof assistant](https://coq.inria.fr/).

This work has been submitted to the journal of ACM Transactions on Computational Logic and it is under review now.

**Note:** exa_b.v represents an Example a.b in the paper.

## Prerequisites

* To compile the files, you will need to have installed Coq on your local machine.

### Installing

* To download and install Coq on your machine, click on the link [install coq](https://coq.inria.fr/download).

### Compile the proofs

* To compile all the files
   ```
   > make
   ```
  - It took about **15 mins** to compile all the files on the **Ubuntu 14.04 LTS** system with **Intel Core i5 3.20 GHz** processor and **8GiB RAM**

* To compile a single file 
  ```
  > coqc filename.v
  ```

* To generate a new `Makefile` by typing
  ```
  > coq_makefile -install none -I . *.v -o Makefile
  ```

* HTML Coqdoc files can be generated by
  ```
  > coqdoc --html --toc --coqlib http://coq.inria.fr/stdlib/ -d _dirname_ *.v
  ```
* The directory webpages/coqdoc contains all the html files of the corresponding .v files

## Authors

* **Ajay Kumar Eeralla** --University of Missouri-Columbia

## Copy Right Information
Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>, University of Missouri-Columbia, USA       

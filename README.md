#### Machine-checked proofs of real-or-random secrecy (Diffie-Hellman protocol), and authentication (Station-to-Station protocol) in Coq
Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>, Rohit Chadha <chadhar@missouri.edu>            
Licensed under the MIT license, see the LICENSE file or http://en.wikipedia.org/wiki/Mit_license                             

[//]: # (The directory machine-checked-proofs contains proofs of security properties, real-or-random secrecy of the Diffie-Hellman protocol, and authentication of the Station-to-Station protocol, and are written in Coq.)
**Note:** exa_b.v represents an Example a.b in the paper.

### Prerequisites

* To compile the files, you will need to have installed Coq on your local machine.

### Installing

* To download and install Coq on your machine, follow the link [install coq](https://coq.inria.fr/download) here.

### Compile the proofs

* The directory machine-checked-proofs already has **Makefile** in it.

* In order to compile all the files, use the command **make**.
  * It took about **one and a half hours** to compile all the files on the system with specifications: **Ubuntu 14.04 LTS**, **Intel Core i5 3.20 GHz**, and  **8GiB RAM**

* To compile a single file _file.v_, you could use **coqc** command. For example, coqc _file.v_.

* To generate a new Makefile by typing

  **coq_makefile -install none -I . *.v -o Makefile**

* HTML Coqdoc files can be generated by
  **coqdoc --html --toc --coqlib http://coq.inria.fr/stdlib/ -d _dirname_ *.v**


## Authors

* **Ajay Kumar Eeralla** --University of Missouri-Columbia
* **Rohit Chadha** -- University of Missouri-Columbia
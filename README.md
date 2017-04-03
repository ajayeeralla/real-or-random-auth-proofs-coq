#### Machine-checked proofs of real-or-random secrecy (Diffie-Hellman protocol), and authentication (Station-to-Station protocol) in Coq
Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>, Rohit Chadha <chadhar@missouri.edu>            
Licensed under the MIT license, see the LICENSE file or http://en.wikipedia.org/wiki/Mit_license                             

[//]: ( The directory machine-checked-proofs contains proofs of security properties, real-or-random secrecy of the Diffie-Hellman protocol, and authentication of the Station-to-Station protocol, and are written in Coq.)

### Prerequisites

To compile the files, you will need to have installed Coq on your local machine.

### Installing

To download and install Coq on your machine, follow the link [install coq](https://coq.inria.fr/download) here.

### Compile the Proofs

The directory machine-checked-proofs already has **Makefile** in it.
In order to compile all the files, use the command **make**.
To compile a single file _file.v_, you could use **coqc** command. For example, coqc _file.v_.

### File Dependency List
The following files are in the order. For example, first file should be compiled before second and so on.

1. definitions.v 
2. morphisms.v 
3. axioms.v 
4. IFTF.v 
5. IFIDEMP.v 
6. IFMORPH.v
7. andbprops.v
8. IFTF.v 
9. IFIDEMP.v 
10. IFMORPH.v 
11. ex9.v 
12. ex10.v 
13. cor_ex10.v 
14. ex11.v 
15. ex12.v 
16. eqbranch.v 
17. ex13.v 
18. ex14.v 
19. ex15.v 
20. ex16.v 
21. ex17.v 
22. ex19.v 
23. ex20.v 
24. auxthms.v 
    1. DHprot.v
        1. real_or_random.v
    2. dsaxioms.v 
        1. auth.v


## Authors

* **Ajay Kumar Eeralla** --University of Missouri-Columbia
* **Rohit Chadha** -- University of Missouri-Columbia
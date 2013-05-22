SASP-Project
============

All our Coq formalizations have been placed in the file src/SLImp/ILImp.v
The rest of the files Coq are dependencies or examples.

All the Coq files can be build using the makefile in src/SLImp/makefile.
Type 'make all' to build.

Dependencies:
   The Coq Containers Library
	http://coq.inria.fr/pylons/contribs/view/Containers/v8.4

   
   Coq v8.4pl1
	http://coq.inria.fr/
	Note that we have only managed to build the containers
	library successfully using the pl1 version.
###############################################################################
###############################################################################
###
### README (for dd_functions SAGE package)
###
###############################################################################
###############################################################################

dd_functions is a SAGE package free to get from the git repository
http://git.risc.jku.at/gitweb/?p=ajpastor/diff_defined_functions.git/
hosted by RISC (Research Intitute for Symbolic Computation).

This package was developed in the research funded by the Austrian Science Fund 
(FWF): W1214-N15, project DK15.

###############################################################################

In this repository several files can be found int root folder:

    - Makefile: a Makefile used for easy distribution of this repository. We do 
    NOT recommend to use it.
    - SPKG.txt: general information file with the description of the project the
    name and email address of the author, and the License under which this project
    was developed.
    - dependencies: a file for the installation of the package in other SAGE systems.
    It contains no dependencies.
    - package-version.txt: a file with the number of the current version distributed
    in this repository.
    - setup.py: the installation file for this package. WARNING: this file and
    installation has not been tested.
    - type: file containing the keyword for the type of SAGE pakage this is. Currently
    it is "optional".
    - README.txt: the present file.
    
These files are not intended to be currently used by the user of this package since
the setup file has not been yet tested. Within this root folder, two main folders
can be found:

    - ajpastor: the main folder with the Python-compiled source code. This is the 
    main folder the user should be concerned for. 
    The user can add this file to the SAGE searching path (in the init.sage file
    of their SAGE distribution), or run SAGE from the root folder of the repository.
    
    This would give direct access to the sode developed in this project with the 
    following syntax:
        sage: from ajpastor.dd_functions import *
    If some particualr package want to be loaded, just use the usual python import
    notation naming the package aftes the "ajpastor" initial folder.
        EXAMPLE: sage: from ajpastor.operator.OreOperator import *;
        
    - releases: in this folder the current version and older releases for the coded 
    are stored (in .zip format). This files are named in the following way:
        diff_defined_functions__XX.zip
    where "XX" is the number of the version of the project they contain.
    Inside this folder another directory can be found. This zip files follows the 
    same convention for naming as in the "releases" folder, but it add also the 
    date and hour this version was commited to the repository.
    
###############################################################################
    named "old". Inside this fodler one can find the same kind of .zip files
    for all the intermidiate releases for the code.

# **DD-finite functions in Sage**

`dd_functions` is a Sage package free to get from the git repository http://git.risc.jku.at/gitweb/?p=ajpastor/diff_defined_functions.git/ hosted by RISC (Research Intitute for Symbolic Computation). This package was developed in the research funded by the Austrian Science Fund  (FWF): W1214-N15, project DK15.

This package allows Sage users to use _naturally_ DD-finite functions on the computer. This README includes a guide to how to install the package.

## **1. Installing the package**
There are three different ways to obtain the package.

#### **Public _git_ repository**
The package can be obtained freely from the public _git_ repository from RISC (Research Institute for Symbolic Computation): click [here](http://git.risc.jku.at/gitweb/?p=ajpastor/diff_defined_functions.git) for the webpage view or [clone](git.risc.jku.at:pub/ajpastor/diff_defined_functions) the repository (git.risc.jku.at:pub/ajpastor/diff_defined_functions).

* This method allow the user to get the <font color="green">very last version</font> of the code.
* From time to time, this means the version <font color="red">is not stable</font>.

#### **Zip download from Webpage**
The last <font color="green">stable version</font> of the code is always available on my [personal webpage](https://www.dk-compmath.jku.at/people/antonio). Just download it and unpack it. To update the code, <font color="red">redownload the zip file and update the folder manually</font>.

##### **How to actually use the package**
Once the repository is cloned or the zip is unpacked, one can run Sage inside the folder or add it to the standars PATH for Sage for look for packages modifying the file `~/.sage/sage.init` and adding the following lines:

`import sys, os;
sys.path.append(os.path.expanduser("###");`
    
where `###` is the path to the local copy of the package.

#### **PiPy installation (<font color="red">not available</font>)**
As the package is implemented in Python 2.7, we can use the following pip command:

`pip install dd_functions`

Using this method will provide <font color="green">the last stable version</font> with an <font color="green">easy way to update</font>.

## **2. Using the package**
Now that the package is installed, we can start using it importing the appropriate package:

`from ajpastor.dd_functions import *`

Or start a Jupyter notebook session for Sage and launch the demo contained in `dd_functions_demo.ipynb`.

# **DD-finite functions in Sage** [![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/Antonio-JP/dd_functions.git/master?filepath=dd_functions_demo.ipynb)

`dd_functions` is a Sage package free to get from the git repository in https://github.com/Antonio-JP/dd_functions.git (GitHub). This package was developed in the research funded by the Austrian Science Fund  (FWF): W1214-N15, project DK15.

This package allows Sage users to use _naturally_ DD-finite functions on the computer. This README includes a guide to how to install the package. For a extensive documentation
of the package, please visit the url https://antonio-jp.github.io/dd_functions/.

## **1. Installing the package**
There are three different ways to obtain the package.

#### **From Source Code**
The package can be obtained freely from the public _git_ repository on GitHub: click [here](https://github.com/Antonio-JP/dd_functions) for the webpage view or clone the repository by [https](https://github.com/Antonio-JP/dd_functions.git) or download the last [zip](https://github.com/Antonio-JP/dd_functions/archive/master.zip).

* This method allow the user to get the <font color="green">very last version</font> of the code.
* After cloning the repository (or getting it in a zip file), use the command `make install` inside the main folder
  to install it.

#### **PiPy installation**
Another option to install and use the package is the use of _pip_ within _Sage_. To do so you have the following options:
* Use the git repository for installation:
  
  `sage -pip install git+https://github.com/Antonio-JP/dd_functions.git`

## **2. Using the package**
Now that the package is installed, we can start using it importing the appropriate package:

`from ajpastor.dd_functions import *`

Or start a Jupyter notebook session for Sage (launching `sage -n jupyter`) and launch the demo contained in `dd_functions_demo.ipynb`.

If you did not want to install the package (or simply, you do not have Sage) do not worry, you can still try it at Binder:
https://mybinder.org/v2/gh/Antonio-JP/dd_functions.git/master?filepath=dd_functions_demo.ipynb [![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/Antonio-JP/dd_functions.git/master?filepath=dd_functions_demo.ipynb)

## **3. External dependencies**
This package installs the *ore_algebra* package from M. Kauers and M. Mezzarobba (see their *git* repository [here](https://github.com/mkauers/ore_algebra)).
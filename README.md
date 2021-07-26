
# DD-finite functions in Sage [![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/Antonio-JP/dd_functions.git/master?filepath=dd_functions_demo.ipynb)

**dd_functions** is a [SageMath](https://www.sagemath.org) package
to work with differentiably definable functions.

These generalise the class of differentially finite or "D-finite" functions:

- D-finite functions satisfy linear differential equations
  with polynomial coefficients
- DD-finite functions satisfy linear differential equations
  with D-finite functions as coefficients
- differentiably definable functions are obtained by iterating this

This package allows Sage users to _naturally_ use DD-finite functions on the computer.

- author: Antonio Jimenez-Pastor
- license: GNU General Public License v3.0
- home page: https://github.com/Antonio-JP/dd_functions
- documentation: https://antonio-jp.github.io/dd_functions/
- online demo: [![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/Antonio-JP/dd_functions.git/master?filepath=dd_functions_demo.ipynb)

This README includes an installation guide.

For extensive documentation, see the documentation link.

Acknowledgements. This package was developed in the research
funded by the Austrian Science Fund (FWF): W1214-N15, project DK15.

## Installation

There are several ways to install the package
(and the online demo requires no installation).

### Install from source code

The package can be obtained from the public _Git_ repository on GitHub:

- click [here](https://github.com/Antonio-JP/dd_functions) for the webpage view
- or clone the repository by [https](https://github.com/Antonio-JP/dd_functions.git)
- or download the latest [zip](https://github.com/Antonio-JP/dd_functions/archive/master.zip).

This method allows the user to get the *very last version* of the code.

After cloning the repository (or getting the zip file and extracting it),
change to the main folder and install by running the command
```
make install
```

### Install via pip

Another option is to install the package using _pip_,
Python's package-management system.

To do so, run the following in a terminal:
```
sage --pip install git+https://github.com/Antonio-JP/dd_functions.git
```

## Usage

Once installed, start Sage and use appropriate imports:
```python
sage: from ajpastor.dd_functions import *
```
Or launch the demo notebook
[`dd_functions_demo.ipynb`](https://github.com/Antonio-JP/dd_functions/blob/master/dd_functions_demo.ipynb).

The package can also be tried online via Binder, see the
"launch Binder" button at the top of this README.
This starts a Sage session on an online server without
requiring any installation on your computer.

## Dependencies

This package

- works on top of [SageMath](https://www.sagemath.org)
- installs the [*ore_algebra*](https://github.com/mkauers/ore_algebra)
  Sage package by M. Kauers and M. Mezzarobba.

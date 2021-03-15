## -*- encoding: utf-8 -*-
import os
import sys
from setuptools import setup
from codecs import open # To open the README file with proper encoding

# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename,  encoding='utf-8') as f:
        return f.read()
    
setup(
    name = "dd_functions",
    version = readfile("VERSION").strip(), # the VERSION file is shared with the documentation
    description='A Sage package for DD-finite functions',
    # long_description = readfile("README.txt"), # get the long description from the README
    # For a Markdown README replace the above line by the following two lines:
    long_description = readfile("README.md"),
    long_description_content_type="text/markdown",
    url='https://www.dk-compmath.jku.at/Members/antonio/sage-package-dd_functions',
    author = "Antonio Jimenez-Pastor",
    author_email = "antonio.jimenez-pastor@dk-compmath.jku.at",
    license = "GPLv3+", # See LICENCE file
    classifiers=[
      # How mature is this project? Common values are
      #   3 - Alpha
      #   4 - Beta
      #   5 - Production/Stable
      'Development Status :: 4 - Beta',
      'Intended Audience :: Science/Research',
      'Topic :: Software Development :: Build Tools',
      'Topic :: Scientific/Engineering :: Mathematics',
      'License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)',
      'Programming Language :: Python :: 3.8.5',
    ], # classifiers list: https://pypi.python.org/pypi?%3Aaction=list_classifiers
    keywords = "holonomic SageMath dfinite",
    packages = ["ajpastor",
        "ajpastor.dd_functions",
        "ajpastor.operator",
        "ajpastor.lazy",
        "ajpastor.misc"],
    setup_requires   = [],
    install_requires = ['ore_algebra @ git+https://github.com/mkauers/ore_algebra.git','sphinx'],
)
    

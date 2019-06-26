
## -*- encoding: utf-8 -*-
import os;
import sys;
from setuptools import setup;
from codecs import open; # To open the README file with proper encoding
from setuptools.command.test import test as TestCommand; # for tests

# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename,  encoding='utf-8') as f:
        return f.read()

# For the tests
class SageTest(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t --force-lib sage_sample")
        if errno != 0:
            sys.exit(1)

setup(
    name = "ajpastor",
    version = readfile("VERSION").strip(), # the VERSION file is shared with the documentation
    description='Sage-based package for DD-finite functions',
    #long_description = readfile("README.rst"), # get the long description from the README
    # For a Markdown README replace the above line by the following two lines:
    #  long_description = readfile("README.md"),
    #  long_description_content_type="text/markdown",
    url='https://www.dk-compmath.jku.at/Members/antonio/sage-package-dd_functions',
    author='Antonio Jimenez-Pastor',
    author_email='ajpastor@risc.uni-linz.ac.at', # choose a main contact email
    license='GPLv3+', # This should be consistent with the LICENCE file
    classifiers=[
      # How mature is this project? Common values are
      #   3 - Alpha
      #   4 - Beta
      #   5 - Production/Stable
      'Development Status :: 3 - Alpha',
      'Intended Audience :: Science/Research',
      'Topic :: Software Development :: Build Tools',
      'Topic :: Scientific/Engineering :: Mathematics',
      'License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)',
      'Programming Language :: Python :: 2.7.15',
    ], # classifiers list: https://pypi.python.org/pypi?%3Aaction=list_classifiers
    keywords = "SageMath packaging",
    packages = ["ajpastor", "ajpastor.dd_functions", "ajpastor.operator", "ajpastor.lazy", "ajpastor.misc", "ajpastor.tests"],
    cmdclass = {'test': SageTest}, # adding a special setup command for tests
    setup_requires   = ['sage-package'],
    install_requires = ['sage-package', 'sphinx'],
)
    

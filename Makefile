SHELL:=/bin/bash

# Package folder
PACKAGE = ajpastor
BASE=ajpastor

# change to your sage command if needed
SAGE = sage

# zip name
ZIP=diff_defined_functions
# version short-cut
VERSION=$(shell cat ./VERSION)


# All command
all: install test

# Installing commands
install:
	$(SAGE) -pip install --upgrade --no-index -v .

uninstall:
	$(SAGE) -pip uninstall $(PACKAGE)

develop:
	$(SAGE) -pip install --upgrade -e .

test:
	$(SAGE) setup.py test

# Documentation commands
coverage:
	$(SAGE) -coverage $(PACKAGE)/*

doc:
	cd docs && $(SAGE) -sh -c "make html"

doc-pdf:
	cd docs && $(SAGE) -sh -c "make latexpdf"

# Creating basic commands
create:
	@echo "Creating main directories..."
	@mkdir -p ./$(BASE)
	@mkdir -p ./releases/old
	@echo "from pkgutil import extend_path;" > ./$(BASE)/__init__.py
	@echo "__path__ = extend_path(__path__, __name__);" >> ./$(BASE)/__init__.py
	
# Zip commands
zip: clean-pyc
	@echo "Compressing the project into file" $(ZIP)".zip"...
	@rm -f ./releases/$(ZIP)__$(VERSION).zip
	@zip -r ./releases/$(ZIP)__$(VERSION).zip $(BASE) type SPKG.txt setup.py package-version.txt Makefile dependencies
	@cp ./releases/$(ZIP)__$(VERSION).zip ./releases/old/$(ZIP)__$(VERSION)__`date +'%y.%m.%d_%H:%M:%S'`.zip
	@cp ./releases/$(ZIP)__$(VERSION).zip ./releases/$(ZIP).zip
	
# Clean commands
clean: clean-pyc clean-doc

clean-pyc:
	@echo "Cleaning the Python precompiled files (.pyc)"
	@find . -name "*.pyc" -exec rm {} +

clean-doc:
	cd docs && $(SAGE) -sh -c "make clean"
	
# git commands
git: zip
	@echo "Pushing changes to public git repository"
	@git add -A
	@git commit
	@git push

.PHONY: all install develop test coverage clean clean-doc doc doc-pdf

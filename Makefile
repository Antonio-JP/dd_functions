SHELL:=/bin/bash
ZIP=dd_functions# ZIP name
VERSION=$(shell cat ./VERSION)

# change to your sage command if needed
SAGE=sage

# Package folder
PACKAGE=ajpastor

all: install doc test
	
create:
	@echo "Creating main directories..."
	@mkdir -p ./$(PACKAGE)
	@mkdir -p ./releases/old
	@echo "from pkgutil import extend_path;" > ./$(PACKAGE)/__init__.py
	@echo "__path__ = extend_path(__path__, __name__);" >> ./$(PACKAGE)/__init__.py
	
# Installing commands
install:
	$(SAGE) -pip install --upgrade .

no-deps:
	$(SAGE) -pip install --upgrade --no-deps .

uninstall:
	$(SAGE) -pip uninstall $(PACKAGE)

develop:
	$(SAGE) -pip install --upgrade -e .

test: install
	$(SAGE) -t $(PACKAGE)

coverage:
	$(SAGE) -coverage $(PACKAGE)/*
	
# Documentation commands
doc: no-deps
	cd docs && $(SAGE) -sh -c "make html"

doc-pdf:
	cd docs && $(SAGE) -sh -c "make latexpdf"
	
# Distribution commands
	
zip: clean
	@echo "Compressing the project into file" $(ZIP)".zip"...
	@rm -f ./releases/$(ZIP)__$(VERSION).zip
	@zip -r ./releases/$(ZIP)__$(VERSION).zip $(PACKAGE) type SPKG.txt setup.py package-version.txt Makefile dependencies
#	@cp ./releases/$(ZIP)__$(VERSION).zip ./releases/old/$(ZIP)__$(VERSION)__`date +'%y.%m.%d_%H:%M:%S'`.zip
	@cp ./releases/$(ZIP)__$(VERSION).zip ./releases/$(ZIP).zip
	
# Cleaning commands
clean: clean_doc clean_pyc

clean_doc:
	@echo "Cleaning documentation"
	@cd docs && $(SAGE) -sh -c "make clean"
	
clean_pyc:
	@echo "Cleaning the Python precompiled files (.pyc)"
	@find . -name "*.pyc" -exec rm {} +

.PHONY: all install develop test coverage clean clean_doc doc doc-pdf
	

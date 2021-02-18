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
	$(SAGE) -t --force-lib .

coverage:
	$(SAGE) -coverage $(PACKAGE)/*
	
# Documentation commands
doc: no-deps
	cd docsrc && $(SAGE) -sh -c "make html"

doc-github: doc
	cp -a docsrc/build/html/. ./docs
		
# Cleaning commands
clean: clean_doc clean_pyc

clean_doc:
	@echo "Cleaning documentation"
	@cd docsrc && $(SAGE) -sh -c "make clean"
	
clean_pyc:
	@echo "Cleaning the Python precompiled files (.pyc)"
	@find . -name "*.pyc" -exec rm {} +

.PHONY: all install develop test coverage clean clean_doc doc doc-pdf
	

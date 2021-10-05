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

lint:
	@echo "Applying Pylint to package"
	@~/sage/local/bin/pylint $(PACKAGE) --disable=all --enable=F,unreachable,duplicate-key,unnecessary-semicolon,\
	global-variable-not-assigned,unused-variable,unused-wildcard-import,binary-op-exception,\
	bad-format-string,anomalous-backslash-in-string,bad-open-mode,E0001,E0011,E0012,E0100,\
	E0101,E0102,E0103,E0104,E0105,E0107,E0108,E0110,E0111,E0112,E0113,E0114,E0115,E0116,E0117,\
	E0118,E0202,E0203,E0211,E0213,E0236,E0237,E0238,E0239,E0240,E0241,E0301,E0302,E0303,E0401,\
	E0402,E0601,E0602,E0603,E0604,E0611,E0632,E0633,E0701,E0702,E0703,E0704,E0710,E0711,E0712,\
	E1003,E1101,E1102,E1111,E1120,E1121,E1123,E1124,E1125,E1126,E1127,E1128,E1129,E1130,E1131,\
	E1132,E1133,E1134,E1135,E1136,E1137,E1138,E1139,E1200,E1201,E1205,E1206,E1300,E1301,E1302,\
	E1303,E1304,E1305,E1306,E1310,E1700,E1701,unused-import,unused-argument \
	--msg-template='{line},{column},{category},{symbol}:{msg}' --reports=n --output-format=text

.PHONY: all install develop test coverage clean clean_doc doc doc-pdf
	

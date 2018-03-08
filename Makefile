SHELL:=/bin/bash
BASE=ajpastor
ZIP=diff_defined_functions# ZIP name
VERSION=$(shell cat ./package-version.txt)

all: 
	sage -sh sage-pip-install .
	
create:
	@echo "Creating main directories..."
	@mkdir -p ./$(BASE)
	@mkdir -p ./releases/old
	@echo "from pkgutil import extend_path;" > ./$(BASE)/__init__.py
	@echo "__path__ = extend_path(__path__, __name__);" >> ./$(BASE)/__init__.py
	
zip:
	@echo "Compressing the project into file" $(ZIP)".zip"...
	@rm -f ./releases/$(ZIP)__$(VERSION).zip
	@zip -r ./releases/$(ZIP)__$(VERSION).zip $(BASE) type SPKG.txt setup.py package-version.txt Makefile dependencies
	@cp ./releases/$(ZIP)__$(VERSION).zip ./releases/old/$(ZIP)__$(VERSION)__`date +'%y.%m.%d_%H:%M:%S'`.zip
	
git:
	@echo "Pushing changes to public git repository"
	@git add -A
	@git commit
	@git push
    
	

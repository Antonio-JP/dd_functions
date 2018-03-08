def run():
    __LIST_OF_FILES = ["ddFunction", "ddFunction2", "examples", "identities", "hypergeometric", "chebyshev", "bessel"];
    
    import importlib;
    for file_name in __LIST_OF_FILES:
        module = importlib.import_module(__package__+"."+file_name);
        print '###############################################################################'
        print "### Testing file %s" %file_name;
        module.run();
        print '###############################################################################'    

try:
    from .ddFunction import *
except Exception:
    print "Error loading module dd_functions.ddFunction";
try:
    from .ddExamples import *;
except Exception:
    print "Error loading module dd_functions.ddExamples";
try:
    from .symbolic import *;
except Exception:
    print "Error loading module dd_functions.symbolic";
try:
    from .toDiffAlgebraic import *;
except Exception:
    print "Error loading module dd_functions.toDiffAlgebraic";

from pkgutil import extend_path;
__path__ = extend_path(__path__, __name__);


class DebugError(RuntimeError):
    '''
        Error meaning an unexpected error in the code. Future versions should fix it.
    '''
    def __init__(self, message):
        RuntimeError.__init__(self, "Debug Error found (%s): we are working in fixing it. Please be patient.\nFIXING TIME!" %message); 

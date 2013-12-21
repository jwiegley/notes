	private AppContext newAppContext( String sModuleName )
	{
		PyObject module = imp.load( sModuleName );
		PyObject object = module.__getattr__( sModuleName );
		return (AppContext) object.__call__( Py.java2py( object ) ).__tojava__(AppContext.class);
	}


	private AppContext newAppContext( String sModuleName )
	{
		PyObject oAppContext = imp.load( sModuleName );
		oAppContext = oAppContext.__getattr__( sModuleName );
		return (AppContext) oAppContext.__call__().__tojava__(AppContext.class);
	}


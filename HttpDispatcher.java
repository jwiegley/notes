	private PyObject newFromModule( String sModuleName, AppContext oAppContext )
	{
		PyModule module = new PyModule("main", new PyStringMap());
		PyObject locals = module.__dict__;

		log( "import " + sModuleName );

		Py.exec(Py.compile_flags("import " + sModuleName, "<string>", "exec", null),
				  locals, locals);

		log( "obj = " + sModuleName + "." + sModuleName + "()" );

		locals.__setitem__( "servlet", Py.java2py( this ) );

		String sArgs;
		if ( oAppContext != null )
		{
			locals.__setitem__( "app", Py.java2py( oAppContext ) );
			sArgs = "(servlet, app)";
		}
		else
		{
			sArgs = "(servlet)";
		}

		Py.exec(Py.compile_flags("obj = " + sModuleName + "." + sModuleName + sArgs,
										 "<string>", "exec", null),
				  locals, locals);

		return locals.__finditem__("obj".intern());
	}

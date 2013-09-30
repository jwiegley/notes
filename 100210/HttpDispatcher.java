	private PyObject newFromModule( String sModuleName )
	{
		PyModule module = new PyModule("main", new PyStringMap());
		PyObject locals = module.__dict__;

		log( "import " + sModuleName );

		Py.exec(Py.compile("import " + sModuleName, "<string>", "exec"),
				  locals, locals);

		log( "obj = " + sModuleName + "." + sModuleName + "()" );

		locals.__setitem__( "servlet", Py.java2py( this ) );

		Py.exec(Py.compile("obj = " + sModuleName + "." + sModuleName + "(servlet)",
								 "<string>", "exec"),
				  locals, locals);

		return locals.__finditem__("obj".intern());
	}


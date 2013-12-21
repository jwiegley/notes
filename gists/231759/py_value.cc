  PyObject * py_type_info(value_t& value) {
    if (value.is_long()) {
      return (PyObject *)&PyInt_Type;
    } else {
      object typeobj(object(value).attr("__class__"));
      return typeobj.ptr();
    }
  }

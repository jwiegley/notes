  virtual optional<scope_t&> find_scope(const std::type_info& type,
					bool skip_this = true) {
    for (scope_t * ptr = (skip_this ? parent : this); ptr; ) {
      if (typeid(ptr) == type)
	return *ptr;
      if (child_scope_t * scope = dynamic_cast<child_scope_t *>(ptr))
        ptr = scope->parent;
      else
	ptr = NULL;
    }
    return none;
  }


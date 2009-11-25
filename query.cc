      expr_t::ptr_op_t mask = new expr_t::op_t(expr_t::op_t::VALUE);
      DEBUG("query.mask", "Mask from string: " << *tok.value);
      mask->set_value(mask_t(*tok.value));
      DEBUG("query.mask", "Mask is: " << mask->as_value().as_mask().str());

   def sorted_cols(cols)
   {
      return (cols
              .trim()
              .toUpperCase()
              .replaceAll(/:/, ',')
              .split(/\s*,\s*/)
              .sort()
              .join(', '))
   }

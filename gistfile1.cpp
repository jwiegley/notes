class ounistream : public std::basic_ostream<UChar>
{
public:
  class outbuf : public std::basic_streambuf<UChar>
  {
  protected:
    UFILE * out;

  public:
    outbuf () : out(NULL) {}
    outbuf (FILE * file_handle) {
      out = u_finit(file_handle, "UTF-8", NULL);
    }
    outbuf (UFILE * ufile_handle) : out(ufile_handle) {}
    outbuf (const boost::filesystem::path& pathname) {
      out = u_fopen(pathname.string().c_str(), "r", "UTF-8", NULL);
    }
    ~outbuf() {
      u_fclose(out);
    }

  protected:
    // write one character
    virtual int_type overflow (int_type c) {
#if 0
      if (c != EOF) {
	char z = c;
	if (write (fd, &z, 1) != 1) {
	  return EOF;
	}
      }
#endif
      return c;
    }
    // write multiple characters
    virtual
    std::streamsize xsputn (const UChar* s, std::streamsize num) {
      return u_file_write(s,num,out);
    }
  };

protected:
  outbuf buf;

public:
  ounistream () : std::basic_ostream<UChar>(0), buf() {}

  ounistream (FILE * file_handle)
    : std::basic_ostream<UChar>(0), buf(file_handle) {
    rdbuf(&buf);
  }
  ounistream (UFILE * ufile_handle)
    : std::basic_ostream<UChar>(0), buf(ufile_handle) {
    rdbuf(&buf);
  }
  ounistream (const boost::filesystem::path& pathname)
    : std::basic_ostream<UChar>(0), buf(pathname) {
    rdbuf(&buf);
  }

  ounistream& operator<<(const UnicodeString& unistr) {
    out << unistr.getBuffer();
    return out;
  }
};

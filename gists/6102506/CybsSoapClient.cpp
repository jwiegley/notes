void initialize_soap_client(
  const char *_merchant_id,
  const char *_transaction_key,
  const char *_cacerts_file,
  const char *_server_url,
  const bool _soap_debugging_mode)
{
  if (MERCHANT_ID == NULL) {
    printf("setting MERCHANT_ID..\n");
    MERCHANT_ID     = strdup(_merchant_id);
    TRANSACTION_KEY = strdup(_transaction_key);
    CACERTS_FILE    = strdup(_cacerts_file);
    SERVER_URL      = strdup(_server_url);

    if (!soap_client_initialized) {
      // one-time initializations
      printf("initialize_soap_client..\n");
      signal(SIGPIPE, sigpipe_handle);
      soap_ssl_init();
      soap_client_initialized = true;
    }
  }
  soap_debugging_mode = _soap_debugging_mode;
}

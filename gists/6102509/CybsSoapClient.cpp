void shutdown_soap_client()
{
  printf("shutdown_soap_client..\n");
  if (MERCHANT_ID)
    free(static_cast<void *>(const_cast<char *>(MERCHANT_ID)));
  if (TRANSACTION_KEY)
    free(static_cast<void *>(const_cast<char *>(TRANSACTION_KEY)));
  if (CACERTS_FILE)
    free(static_cast<void *>(const_cast<char *>(CACERTS_FILE)));
  if (SERVER_URL)
    free(static_cast<void *>(const_cast<char *>(SERVER_URL)));
}

<wsse:Security soapenv:actor="http://www.jStartcustomer.com/actors#verifier" 
               soapenv:mustUnderstand="1" 
               xmlns:wsse="http://schemas.xmlsoap.org/ws/2002/04/secext">
  <Signature xmlns="http://www.w3.org/2000/09/xmldsig#">
    <SignedInfo>
      <CanonicalizationMethod Algorithm="http://www.w3.org/2001/10/xml-exc-c14n#"/>
      <SignatureMethod Algorithm="http://www.w3.org/2000/09/xmldsig#rsa-sha1"/>
      <Reference URI="#sign_content_1043176028580">
        <Transforms>
          <Transform Algorithm="http://www.w3.org/2001/10/xml-exc-c14n#"/>
        </Transforms>
        <DigestMethod Algorithm="http://www.w3.org/2000/09/xmldsig#sha1"/>
        <DigestValue>FLuQTa/LqDIZ5F2JSaMRHSRuaiQ=</DigestValue>
      </Reference>
    </SignedInfo>

    <SignatureValue>
      kGlrrXjKku/WXKxID+JJkEXY+aGNYHc5dy8GwbLFtB5Msll2/MhwdnO9wastJ0gLPzLy3oHL
      7A8ggkMkjgAqnLg6PTzM7MdKoIAhe+xRHdOysamGucFJQRMrU+JQ4WATJt0bpdClwJy6mexT
      Su48mq1q5rM9YZh61P7UEUKt+EQ=
    </SignatureValue>

    <KeyInfo xmlns="http://www.w3.org/2000/09/xmldsig#">
      <KeyValue>
        <RSAKeyValue>
          <Modulus>
            2sW+eBjx5D2QMyr8ocZIZWNYHGf9zYhB4XWILPCTvhNV7dIe3l8ARepOA1ABFK2OMy
            pzb+Rb+nWQeo//yFz/28PmL63kdLiE72qmmQuzuPa5NXaV9pJ4JKw86QdLhGGpFIRH
            18Iugf3xLFwQEZqKYnblTUs7ftnTgW5r4HH492k=
          </Modulus>
          <Exponent>AQAB</Exponent>
        </RSAKeyValue>
      </KeyValue>

      <X509Data>
        <X509IssuerSerial>
          <X509IssuerName>OU=Java,O=IBM,L=Unknown,ST=Oklahoma,C=US</X509IssuerName>
        <X509SerialNumber>0</X509SerialNumber></X509IssuerSerial>
        <X509SubjectName>CN=John Doe</X509SubjectName>
        <X509Certificate>
          MIIB0TCCAToCAQAwDQYJKoZIhvcNAQEEBQAwTzELMAkGA1UEBhMCVVMxETAPBgNVBAgTCE9rbGFo
          b21hMRAwDgYDVQQHEwdVbmsam3duMQwwCgYDVQQKEwNJQk0xDTALBgNVBAsTBEphdmEwHhcNMDIw
          OTI1MTAxMTQ4WhcNMDMwOTI1MTAxMTQ4WjATMREwDwYDVQQDEwhKb2huIERvZTCBnzANBgkqhkiG
          9w0BAQEFAAOBjQAwgYkCgYEA2sW+eBjx5D2QMyr8ocZIZWNYHGf9zYhB4XWILPCTvhNV7dIe3l8A
          RepOA1ABFK2OMypzb+Rb+nWQeo//yFz/28PmL63kdLiE72qmmQuzuPa5NXaV9pJ4JKw86QdLhGGp
          FIRH18Iugf3xLFwQEZqKYnblTUs7ftnTgW5r4HH492kCAwEAATANBgkqhkiG9w0BAQQFAAOBgQCs
          OD02WMoYcMR7Sqdb9oQyk7Nn4rQ5DBgZ5mxGGVzWxBZW/QON+Ir2j4KUjX1jalMvbHa9lnhPQmJi
          Ued923rza7fvdRG2CDalbW0R3aPd5q0u3akP0/Ejb7z5o88heajCSgfRruvU+ZdOTT3Oe+RBQgw8
          VuzbLApPnXiehowYuA==
        </X509Certificate>
      </X509Data>
    </KeyInfo>
  </Signature> 
</wsse:Security>

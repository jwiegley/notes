package com.cybersource.sample;
import com.cybersource.ws.client.Client;
import com.cybersource.ws.client.ClientException;
import com.cybersource.ws.client.FaultException;
import com.cybersource.ws.client.Utility;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

public class AuthCaptureSample
{
  public static void main(String[] paramArrayOfString)
  {
    Properties localProperties = Utility.readProperties(paramArrayOfString);

    String str = runAuth(localProperties);
    if (str != null)
    {
      runCapture(localProperties, str);
    }
  }

  public static String runAuth(Properties paramProperties)
  {
    String str1 = null;

    HashMap localHashMap1 = new HashMap();

    localHashMap1.put("ccAuthService_run", "true");

    localHashMap1.put("merchantReferenceCode", "your_merchant_reference_code");

    localHashMap1.put("billTo_firstName", "John");
    localHashMap1.put("billTo_lastName", "Doe");
    localHashMap1.put("billTo_street1", "1295 Charleston Road");
    localHashMap1.put("billTo_city", "Mountain View");
    localHashMap1.put("billTo_state", "CA");
    localHashMap1.put("billTo_postalCode", "94043");
    localHashMap1.put("billTo_country", "US");
    localHashMap1.put("billTo_email", "nobody@cybersource.com");
    localHashMap1.put("billTo_ipAddress", "10.7.7.7");
    localHashMap1.put("billTo_phoneNumber", "650-965-6000");
    localHashMap1.put("shipTo_firstName", "Jane");
    localHashMap1.put("shipTo_lastName", "Doe");
    localHashMap1.put("shipTo_street1", "100 Elm Street");
    localHashMap1.put("shipTo_city", "San Mateo");
    localHashMap1.put("shipTo_state", "CA");
    localHashMap1.put("shipTo_postalCode", "94401");
    localHashMap1.put("shipTo_country", "US");
    localHashMap1.put("card_accountNumber", "4111111111111111");
    localHashMap1.put("card_expirationMonth", "12");
    localHashMap1.put("card_expirationYear", "2020");
    localHashMap1.put("purchaseTotals_currency", "USD");

    localHashMap1.put("item_0_unitPrice", "12.34");
    localHashMap1.put("item_1_unitPrice", "56.78");

    try
    {
      displayMap("CREDIT CARD AUTHORIZATION REQUEST:", localHashMap1);

      HashMap localHashMap2 = Client.runTransaction(localHashMap1, paramProperties);

      displayMap("CREDIT CARD AUTHORIZATION REPLY:", localHashMap2);

      String str2 = (String)localHashMap2.get("decision");
      if ("ACCEPT".equalsIgnoreCase(str2))
      {
        str1 = (String)localHashMap2.get("requestID");
      }

    }
    catch (ClientException localClientException)
    {
      System.out.println(localClientException.getMessage());
      if (localClientException.isCritical())
      {
        handleCriticalException(localClientException, localHashMap1);
      }
    }
    catch (FaultException localFaultException)
    {
      System.out.println(localFaultException.getMessage());
      if (localFaultException.isCritical())
      {
        handleCriticalException(localFaultException, localHashMap1);
      }
    }

    return str1;
  }

  public static void runCapture(Properties paramProperties, String paramString)
  {
    Object localObject = null;

    HashMap localHashMap1 = new HashMap();

    localHashMap1.put("ccCaptureService_run", "true");

    localHashMap1.put("merchantReferenceCode", "MRC-14344");

    localHashMap1.put("ccCaptureService_authRequestID", paramString);

    localHashMap1.put("purchaseTotals_currency", "USD");
    localHashMap1.put("item_0_unitPrice", "12.34");

    try
    {
      displayMap("FOLLOW-ON CAPTURE REQUEST:", localHashMap1);

      HashMap localHashMap2 = Client.runTransaction(localHashMap1, paramProperties);

      displayMap("FOLLOW-ON CAPTURE REPLY:", localHashMap2);
    }
    catch (ClientException localClientException)
    {
      System.out.println(localClientException.getMessage());
      if (localClientException.isCritical())
      {
        handleCriticalException(localClientException, localHashMap1);
      }
    }
    catch (FaultException localFaultException)
    {
      System.out.println(localFaultException.getMessage());
      if (localFaultException.isCritical())
      {
        handleCriticalException(localFaultException, localHashMap1);
      }
    }
  }

  private static void displayMap(String paramString, Map paramMap)
  {
    System.out.println(paramString);

    StringBuffer localStringBuffer = new StringBuffer();

    if ((paramMap != null) && (!paramMap.isEmpty()))
    {
      Iterator localIterator = paramMap.keySet().iterator();

      while (localIterator.hasNext())
      {
        String str1 = (String)localIterator.next();
        String str2 = (String)paramMap.get(str1);
        localStringBuffer.append(str1 + "=" + str2 + "\n");
      }
    }

    System.out.println(localStringBuffer.toString());
  }

  private static void handleCriticalException(ClientException paramClientException, Map paramMap) {}

  private static void handleCriticalException(FaultException paramFaultException, Map paramMap) {}
}
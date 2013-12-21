      try
      {
         try
         {
            return createDocumentPreview( oDocumentID, oSectionID, iWidth, iHeight, iRotation, sMIMEType );
         }
         catch (Exception e)
         {
            e.printStackTrace();
            throw e;
         }
      }
      catch ( IOException e )
      {
         throw new DocumentListException( _oDocumentListBundle.ERROR_ADAGIO, e );
      }

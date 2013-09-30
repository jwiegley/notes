import org.python.core.__builtin__;
import org.python.core.Py;
import org.python.core.PyObject;
import org.python.core.PyString;
import org.python.core.PySystemState;

public class Waitress
{
	public static void main(String[] args)
	{
		PySystemState.initialize();
		PySystemState sys = Py.getSystemState();
		sys.path.append(new PyString("/Users/johnw/Downloads/"));
		if (__builtin__.__import__("BaconSpam") == null)
			System.out.println("__builtin__.__import__(\"BaconSpam\") is null");
		if (__builtin__.__import__("BaconSpam").__getattr__("BaconSpam") == null)
			System.out.println("__builtin__.__import__(\"BaconSpam\").__getattr__(\"BaconSpam\") is null");
			
		PyObject BaconSpam = __builtin__.__import__("BaconSpam").__getattr__("BaconSpam");
		Spam menu = (Spam)BaconSpam.__call__().__tojava__(Spam.class);
		String food = menu.serves();
		System.out.println("We serve " + food + "!");
	}
}

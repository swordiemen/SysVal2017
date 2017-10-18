/**
 * The main class to test the ignition module. Iterate through
 * engine speeds from 2000 RPM to 6000 RPM with step 10 and
 * print the resulting ignition value. 
 */
public class IgnitionTest {

	//@ skipesc;
	public static void main(String[] args) {
		SensorValue rpmSensor = new SensorValue(1000, 0, 8000);
		IgnitionModule im = new IgnitionModule(rpmSensor);
		for(int r=2000; r<6000; r+=10) {
			rpmSensor.readSensor(r);
			System.out.println("RPM: "+rpmSensor.getValue()+", IGN: "+im.getIgnition());
		}
	}
}

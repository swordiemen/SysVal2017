/**
 * An example class that uses the lookup tables library to implement an 
 * ignition module. In this particular example, the values of the table
 * are rotational degrees multiplied by 10 before the synchronization
 * point of the engine (this synchronization is done once per every
 * engine rotation) when the ignition spark should be provided. That is,
 * value 80 states that the spark should occur 8 rotational degrees before
 * the synchronization point.
 */
class IgnitionModule {
	
	SensorValue rpmSensor;
	LookupScale rpmScale = new LookupScale(600, 8000, 16);
	LookupTable1d ignitionTable = new LookupTable1d(rpmScale,
		new int[] { 120,  80,  60,  80, 100, 120, 140, 160,
			         180, 200, 220, 250, 300, 320, 340, 360	});
	
	IgnitionModule(SensorValue rpmSensor) {
		this.rpmSensor = rpmSensor;
	}
	
	int getIgnition() {
		return ignitionTable.getValue(rpmSensor);

	}

}

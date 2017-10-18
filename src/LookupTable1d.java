/**
 * This class encapsulates one dimensional lookup table.
 */
class LookupTable1d {

	/** The only (one dimension, x) scale for this lookup table. */
	//@ invariant scaleX != null;
	LookupScale scaleX;
	
	/** The lookup values of this table. Contrary to the scales 
	 *  there are no sortedness requirements of any kind.
	 */
	//@ invariant lookupValues.length > 1;
	int[] lookupValues;
	
	// INVARIANT
	
	/**
	 * Constructs the lookup table
	 * @param scale the associated (x) scale
	 * @param lookupValues the table values
	 */
	//@ requires scale != null;
	//@ requires lookupValues.length == scale.values.length;
	//@ ensures this.scaleX == scale;
	//@ ensures this.lookupValues == lookupValues;
	LookupTable1d(LookupScale scale, int[] lookupValues) {
		this.scaleX = scale;
		this.lookupValues = lookupValues;
	}
	
	/**
	 * Looks up the sensor value in the this table.
	 * @param sv the sensor value to look up
	 * @return the (interpolated) value from the table
	 */
	//@ requires sv != null;
	//@ ensures \result > 0 && \result < lookupValues[lookupValues.length-1];
	int getValue(SensorValue sv) {
		ScaleIndex si = scaleX.lookupValue(sv);
		int i = si.getIntPart();
		int f = si.getFracPart();
		int v = lookupValues[i];
		if(i<lookupValues.length-1) {
			int vn = lookupValues[i+1];
			//REPORT THIS IS WRONG, needs to be 0.f * vn
			v = v + f;
		}
		// ASSERTION(S)
		if(i == lookupValues.length) {
			assert v == lookupValues[i];
		}else {
			assert v == lookupValues[i] + (f * lookupValues[i+1]) / 100;
		}
		// (note, what you want to check here would normally
		//  be part of the postcondition, but would produce a very
		//  elaborate specification).
		return v;
	}
}

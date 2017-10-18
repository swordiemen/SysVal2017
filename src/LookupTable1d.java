/**
 * This class encapsulates one dimensional lookup table.
 */
class LookupTable1d {

	/** The only (one dimension, x) scale for this lookup table. */
	LookupScale scaleX;
	
	/** The lookup values of this table. Contrary to the scales 
	 *  there are no sortedness requirements of any kind.
	 */
	int[] lookupValues;
	
	// INVARIANT
	
	/**
	 * Constructs the lookup table
	 * @param scale the associated (x) scale
	 * @param lookupValues the table values
	 */
	// CONTRACT 
	LookupTable1d(LookupScale scale, int[] lookupValues) {
		this.scaleX = scale;
		this.lookupValues = lookupValues;
	}
	
	/**
	 * Looks up the sensor value in the this table.
	 * @param sv the sensor value to look up
	 * @return the (interpolated) value from the table
	 */
	int getValue(SensorValue sv) {
		ScaleIndex si = scaleX.lookupValue(sv);
		int i = si.getIntPart();
		int f = si.getFracPart();
		int v = lookupValues[i];
		if(i<lookupValues.length-1) {
			int vn = lookupValues[i+1];
			v = v + f;
		}
		// ASSERTION(S)
		// (note, what you want to check here would normally
		//  be part of the postcondition, but would produce a very
		//  elaborate specification).
		return v;
	}
}

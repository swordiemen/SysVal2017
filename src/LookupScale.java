/** This class encapsulates lookup table scales. */

class LookupScale {

	/**
	 * Stores the scale (so called) break points. Scales are required to be strictly
	 * monotone, with raising values.
	 */
	int[] values;

	// INVARIANT(S)
	//@ invariant (\forall int a; 0 <= a && a < this.values.length-1; this.values[a+1] > this.values[a]);
	//@ invariant (\forall int a; a >=0 && a < (this.values.length-2); (this.values[a+2] -this.values[a+1] == (this.values[a+1] - this.values[a])));
	
	/**
	 * Construct the scale with predefined break points
	 * 
	 * @param values
	 *            the array with break point values
	 */
	// CONTRACT
	//@ ensures this.values == values;
	//@ requires values.length > 1;
	LookupScale(int[] values) {
		this.values = values;
	}

	/**
	 * Construct a linear scale that has size break points equally distributed
	 * between min and max values.
	 * 
	 * @param min
	 *            minimal value of the scale
	 * @param max
	 *            maximal value of the scale
	 * @param size
	 *            number of break points in the scale
	 */
	// CONTRACT
	//@ ensures this.values.length == size;
	//@ requires size > 1;
	//@ ensures this.values[0] == min;
	LookupScale(int min, int max, int size) {
		  this.values = new int[size];
		  int chunk = (max - min) / (size - 1);
		  //@ assume values.length > 0;
		  //@ assume chunk > 0;
		  int i;
		  this.values[0] = min;
		  //@ loop_invariant i>0 && i < this.values.length && this.values[i] == this.values[i-1] + chunk;
		  for(i = 1; i < this.values.length; i++) {
		    this.values[i] = this.values[i - 1] + chunk;
		  }
		}

	/**
	 * Looks up a sensor value in the scale and returns the scale index
	 * corresponding to the position of the sensor value in the scale.
	 * 
	 * @param sv
	 *            the sensor value that should be looked up the scale
	 * @return the scale index (integral and fractional part)
	 */
	// CONTRACT
	//@ requires (sv.getValue() == this.values[0]) || (sv.getValue() == this.values[this.values.length -1]) || (sv.getValue() > this.values[0]  &&  sv.getValue() < this.values[this.values.length -1]); 
	//@ requires sv != null;
	//@ ensures \result != null;
	ScaleIndex lookupValue(SensorValue sv) {
		int v = sv.getValue();
		// First get the integral part
		// The most convenient way to lookup scales is from the end
		int intPart = this.values.length - 1;
		while (intPart >= 0) {
			if (v >= this.values[intPart]) {
				break;
			}
			intPart--;
		}
		// ASSERTION
		//@ assert intPart >= 0 || intPart < this.values.length;

		int fracPart = 0;
		// Check border cases
		if (intPart == this.values.length - 1 || v < this.values[0]) {
			// ASSERTION(S)
			//@ assert (intPart == this.values[0]) || (intPart == this.values.length - 1);
			//@ assert fracPart == 0;

			return new ScaleIndex(intPart, fracPart, this.values.length);
		}
		// Then calculate the fractional part
		fracPart = (v - this.values[intPart]) * 100 / (this.values[intPart + 1] - this.values[intPart]);
		// ASSERTION(S)
		//@ assert fracPart == (v - this.values[intPart]) * 100 / (this.values[intPart + 1] - this.values[intPart]);
		return new ScaleIndex(intPart, fracPart, this.values.length);
	}

	/**
	 * Provide a human readable version of this object, makes the output of
	 * JMLUnitNG more readable.
	 */
	// @ skipesc;
	public String toString() {
		String r = "Scale of size " + this.values.length + ": [";
		for (int i = 0; i < this.values.length; i++) {
			r += "" + (i == 0 ? "" : ", ") + values[i];
		}
		r += "]";
		return r;
	}

}

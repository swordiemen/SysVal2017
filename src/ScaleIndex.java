/**
 * An encapsulation class that stores the scale index, that is,
 * its integral and fractional (0..99%) part. It also stores the size
 * of the lookup scale that this index refers to. 
 */
class ScaleIndex {

	/** Integral part. */
	int intPart;
	
	/** Fractional part. */
	int fracPart;
	
	/** The size of the corresponding scale this index refers to. */
	int size;      

	// INVARIANT(S)
	//@ invariant intPart >= 0;
	//@ invariant fracPart >= 0 && fracPart < 100;
	//@ invariant size > 1;
	
	// MODEL

	/**
	 * Constructs a new index with the given parameters.
	 * @param intPart integral part
	 * @param fracPart fractional (0..99) part
	 * @param size the size of the underlying scale
	 */
	//@ requires intPart >= 0;
	//@ requires fracPart >= 0 && fracPart < 100;
	//@ requires size > 1;
	//@ ensures this.intPart == intPart;
	//@ ensures this.fracPart == fracPart;
	//@ ensures this.size == size;
	ScaleIndex(int intPart, int fracPart, int size) {
		this.intPart = intPart;
		this.fracPart = fracPart;
		this.size = size;
	}
	
	/**
	 * @return the integral part
	 */
	//@ pure;
	int getIntPart() {
		return intPart;
	}

	/**
	 * @return the fractional part
	 */
	//@ pure;
	int getFracPart() {
		return fracPart;
	}

	/**
	 * @return the size of the underlying scale
	 */
	//@ pure;
	int getSize() {
		return size;
	}

}

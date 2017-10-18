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
	
	// MODEL

	/**
	 * Constructs a new index with the given parameters.
	 * @param intPart integral part
	 * @param fracPart fractional (0..99) part
	 * @param size the size of the underlying scale
	 */
	// CONTRACT
	ScaleIndex(int intPart, int fracPart, int size) {
		this.intPart = intPart;
		this.fracPart = fracPart;
		this.size = size;
	}
	
	/**
	 * @return the integral part
	 */
	// CONTRACT
	int getIntPart() {
		return intPart;
	}

	/**
	 * @return the fractional part
	 */
	// CONTRACT
	int getFracPart() {
		return fracPart;
	}

	/**
	 * @return the size of the underlying scale
	 */
	// CONTRACT
	int getSize() {
		return size;
	}

}

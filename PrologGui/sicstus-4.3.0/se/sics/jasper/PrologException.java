/*
 * Copyright (c) 2002 SICS AB
 */

package se.sics.jasper;

/**
 * Represents an exception thrown by a Prolog object. User code should catch
 * a PrologException.
 */
public interface PrologException
{
    String toString();

    public Term getTerm() throws Exception;
}

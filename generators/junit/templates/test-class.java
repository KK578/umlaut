package AutomatedTestSuite

import static org.junit.Assert.*;
import org.junit.Test;

import org.junit.Before;

public class <%= classObject.name %>UnitTestClass
{
	<%= classObject.name %> testee;

	@Before
	public void setUp()
	{
		testee = new <%= classObject.name %>();
	}
	<%_ classObject.methods.map((method) => { _%>
	<%_		method.tests.map((test) => { _%>
	<%_			if (test) { %>
	@Test<% if (test.exception) { %>(expected=<%= test.exception.type %>.class)<% } %>
	public void <%= test.name %>()
	{
		<%_ test.args.map((arg) => { _%>
		<%= arg.type %> <%= arg.name %> = <%= arg.value %>;
		<%_ }) _%>

		<%= method.return.type %> result = testee.<%= method.name %>(<%= test.argumentString %>);

		<%_ method.postconditions.map((condition) => { _%>
		assertTrue(<%= condition.arguments[0] %> <%- condition.comparison %> <%= condition.arguments[1] %>);
		<%_ }) _%>
	}
	<%_			} _%>
	<%_ 	}) _%>
	<%_ }) _%>
}

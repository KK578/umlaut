using System;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace AutomatedTestSuite
{
	[TestClass]
	public class <%= classObject.name %>UnitTestClass
	{
		<%= classObject.name %> testee;

		[TestInitialize]
		public void Initialize()
		{
			testee = new <%= classObject.name %>();
		}
		<%_ classObject.methods.map((method) => { _%>
		<%_		method.tests.map((test) => { _%>
		<%_			if (test) { %>
		[TestMethod]
		<%_ 			if (test.exception) { _%>
		[ExpectedException(typeof(<%= test.exception.type %>))]
		<%_ 			} _%>
		public void <%= test.name %>()
		{
			<%_ test.args.map((arg) => { _%>
			<%= arg.type %> <%= arg.name %> = <%= arg.value %>;
			<%_ }) _%>

			<%= method.return.type %> result = testee.<%= method.name %>(<%= test.argumentString %>);

			<%_ method.postconditions.map((condition) => { _%>
			Assert.isTrue(<%= condition.arguments[0] %> <%- condition.comparison %> <%= condition.arguments[1] %>);
			<%_ }) _%>
		}
		<%_			} _%>
		<%_ 	}) _%>
		<%_ }) _%>
	}
}

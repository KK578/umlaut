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
		<% for (var i = 0; i < classObject.methods.length; i++) { _%>
		<%_ for (var j = 0; j < classObject.methods[i].tests.length; j++) { _%>
		<%_ if (classObject.methods[i].tests[j]) { %>
		[TestMethod]
		public void <%= classObject.methods[i].tests[j].name %>()
		{
			testee.<%= classObject.methods[i].name %>(<%= classObject.methods[i].tests[j].argumentString %>);
		}
		<%_ } _%>
		<%_ } _%>
		<%_ } -%>
	}
}

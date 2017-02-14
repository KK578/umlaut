using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace UmlAnnotator
{
	class LinkedOclCondition : OclCondition
	{
		private static string ConvertString(string condition)
		{
			string result = condition;

			// Linked conditions will be present at the start of the condition string, after the '('.
			// Contained within a { } pair of curly braces.
			if (result[1] == '{')
			{
				result = result.Remove(1, result.IndexOf('}') + 1);
			}

			return result;
		}

		private List<OclCondition> linkedConditions;

		public LinkedOclCondition() : base()
		{
			linkedConditions = new List<OclCondition>();
		}

		public LinkedOclCondition(string condition) : base(ConvertString(condition))
		{
			linkedConditions = new List<OclCondition>();

			if (condition[1] == '{')
			{
				string storedLink = condition.Substring(1, condition.IndexOf('}'));
			}
		}
	}
}

// Shared schemas — imported by billing.ts (cross-file resolution demo).
declare const z: any

export const InvoiceSchema = z.object({
  subtotal: z.number().positive(),
  tax: z.number().nonnegative(),
  total: z.number(),
}).refine((i: any) => i.total === i.subtotal + i.tax)
